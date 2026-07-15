//! A sponge that can *conditionally* absorb inputs
//! (port of pickles' `opt_sponge.ml`).
//!
//! Each absorbed element comes with a boolean flag; elements whose flag is
//! false are skipped, with the write position and the permutation schedule
//! tracked in-circuit. Used by the pickles verifiers to hash optional parts
//! of statements (e.g. feature-flag-dependent values).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{poseidon::permute, Boolean, FieldVar, RunState, SnarkyResult};

const M: usize = 3;
const RATE: usize = 2;

/// A flagged sponge input: absorbed iff the boolean is true.
type FlaggedInput<F> = (Boolean<F>, FieldVar<F>);

/// The sponge's mode.
enum SpongeState<F: PrimeField> {
    /// Accumulating flagged inputs (lazily; they are consumed on squeeze).
    Absorbing {
        next_index: Boolean<F>,
        xs: Vec<FlaggedInput<F>>,
    },
    /// `Squeezed(n)`: `n` elements squeezed since the last permutation.
    Squeezed(usize),
}

/// A sponge with conditional absorption.
pub struct OptSponge<F: PrimeField> {
    state: [FieldVar<F>; M],
    sponge_state: SpongeState<F>,
    needs_final_permute_if_empty: bool,
}

impl<F: PrimeField> Default for OptSponge<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> OptSponge<F> {
    pub fn new() -> Self {
        Self {
            state: [FieldVar::zero(), FieldVar::zero(), FieldVar::zero()],
            sponge_state: SpongeState::Absorbing {
                next_index: Boolean::false_(),
                xs: vec![],
            },
            needs_final_permute_if_empty: true,
        }
    }

    /// Continues from a plain sponge in absorbing mode. OCaml switches from
    /// `Sponge` to `Opt_sponge` at the first optional accumulator input; the
    /// pending rate position is therefore part of the protocol state.
    pub fn from_sponge(sponge: crate::sponge::PoseidonSponge<F>) -> Self {
        let (state, absorbed) = sponge.into_var_state_absorbed();
        assert!(absorbed < RATE, "invalid absorbed Poseidon rate position");
        Self {
            state,
            sponge_state: SpongeState::Absorbing {
                next_index: if absorbed == 0 {
                    Boolean::false_()
                } else {
                    Boolean::true_()
                },
                xs: vec![],
            },
            needs_final_permute_if_empty: true,
        }
    }

    /// Queues `(flag, x)`: `x` is absorbed iff `flag` is true.
    pub fn absorb(&mut self, input: FlaggedInput<F>) {
        match &mut self.sponge_state {
            SpongeState::Absorbing { xs, .. } => xs.push(input),
            SpongeState::Squeezed(_) => {
                self.sponge_state = SpongeState::Absorbing {
                    next_index: Boolean::false_(),
                    xs: vec![input],
                }
            }
        }
    }

    pub fn squeeze(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
    ) -> SnarkyResult<FieldVar<F>> {
        match &mut self.sponge_state {
            SpongeState::Squeezed(n) => {
                let n = *n;
                if n == RATE {
                    self.state = permute(sys, loc, self.state.clone());
                    self.sponge_state = SpongeState::Squeezed(1);
                    Ok(self.state[0].clone())
                } else {
                    self.sponge_state = SpongeState::Squeezed(n + 1);
                    Ok(self.state[n].clone())
                }
            }
            SpongeState::Absorbing { next_index, xs } => {
                let (start_pos, input) = (next_index.clone(), std::mem::take(xs));
                let needs = self.needs_final_permute_if_empty;
                consume(sys, loc, needs, start_pos, &input, &mut self.state)?;
                self.needs_final_permute_if_empty = true;
                self.sponge_state = SpongeState::Squeezed(1);
                Ok(self.state[0].clone())
            }
        }
    }

    /// Consumes the opt sponge into `(state, squeezed)` for the opt->plain
    /// conversion of the wrap verifier (`wrap_verifier.ml:1294-1304`, IVC
    /// Step 13). Panics if the sponge is still absorbing, exactly as the
    /// OCaml `assert false` on the `Absorbing` arm.
    pub fn into_squeezed_parts(self) -> ([FieldVar<F>; 3], usize) {
        match self.sponge_state {
            SpongeState::Squeezed(n) => (self.state, n),
            SpongeState::Absorbing { .. } => {
                panic!("OptSponge::into_squeezed_parts: sponge is still absorbing")
            }
        }
    }
}

/// `a[i] += x` where `i` is a boolean position (0 or 1):
/// `a[j] += (i == j) * x` for `j = 0, 1`, via one r1cs constraint each.
fn add_in<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    a: &mut [FieldVar<F>; M],
    i: &Boolean<F>,
    x: &FieldVar<F>,
) -> SnarkyResult<()> {
    let selectors = [i.not(), i.clone()];
    for (j, i_equals_j) in selectors.iter().enumerate() {
        let (a_j, xv, sel) = (a[j].clone(), x.clone(), i_equals_j.clone());
        let a_j_new: FieldVar<F> = sys.compute(
            loc.clone(),
            move |env: &dyn snarky::runner::WitnessGeneration<F>| {
                let a_j = env.read_var(&a_j);
                if env.read_var(&sel.to_field_var()) == F::one() {
                    a_j + env.read_var(&xv)
                } else {
                    a_j
                }
            },
        )?;
        // x * (i == j) = a_j' - a_j
        sys.assert_r1cs(
            Some("opt_sponge add_in".into()),
            loc.clone(),
            x.clone(),
            i_equals_j.to_field_var(),
            &a_j_new - &a[j],
        )?;
        a[j] = a_j_new;
    }
    Ok(())
}

/// Conditionally applies the permutation to the state.
fn cond_permute<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    permute_flag: &Boolean<F>,
    state: &mut [FieldVar<F>; M],
) -> SnarkyResult<()> {
    let permuted = permute(sys, loc.clone(), state.clone());
    for (s, p) in state.iter_mut().zip(permuted) {
        *s = sys.if_(loc.clone(), permute_flag.clone(), p, s.clone())?;
    }
    Ok(())
}

fn consume_pairs<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    state: &mut [FieldVar<F>; M],
    start_pos: Boolean<F>,
    pairs: &[(FlaggedInput<F>, FlaggedInput<F>)],
) -> SnarkyResult<Boolean<F>> {
    let mut p = start_pos;
    for ((b, x), (b2, y)) in pairs {
        let p2 = p.xor(b, sys, loc.clone())?;
        let pos_after = p2.xor(b2, sys, loc.clone())?;

        let y = y.mul(&b2.to_field_var(), None, loc.clone(), sys)?;

        // the only case where y is added after the permutation: b && b2 && p
        let add_in_y_after_perm =
            Boolean::all(&[b.clone(), b2.clone(), p.clone()], sys, loc.clone())?;
        let add_in_y_before_perm = add_in_y_after_perm.not();

        let x_masked = x.mul(&b.to_field_var(), None, loc.clone(), sys)?;
        add_in(sys, loc.clone(), state, &p, &x_masked)?;
        let y_before = y.mul(&add_in_y_before_perm.to_field_var(), None, loc.clone(), sys)?;
        add_in(sys, loc.clone(), state, &p2, &y_before)?;

        // permute iff (b && b2) || (p && (b || b2))
        let b_and_b2 = b.and(b2, sys, loc.clone());
        let b_or_b2 = b.or(b2, loc.clone(), sys);
        let p_and_or = p.and(&b_or_b2, sys, loc.clone());
        let permute_flag = Boolean::any(&[&b_and_b2, &p_and_or], sys, loc.clone())?;

        cond_permute(sys, loc.clone(), &permute_flag, state)?;

        let y_after = y.mul(&add_in_y_after_perm.to_field_var(), None, loc.clone(), sys)?;
        add_in(sys, loc.clone(), state, &p2, &y_after)?;

        p = pos_after;
    }
    Ok(p)
}

fn consume<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    needs_final_permute_if_empty: bool,
    start_pos: Boolean<F>,
    input: &[FlaggedInput<F>],
    state: &mut [FieldVar<F>; M],
) -> SnarkyResult<()> {
    let n = input.len();
    let num_pairs = n / 2;
    let remaining = n - 2 * num_pairs;

    let pairs: Vec<_> = (0..num_pairs)
        .map(|i| (input[2 * i].clone(), input[2 * i + 1].clone()))
        .collect();
    let pos = consume_pairs(sys, loc.clone(), state, start_pos, &pairs)?;

    let flags: Vec<&Boolean<F>> = input.iter().map(|(b, _)| b).collect();
    let empty_input = Boolean::any(&flags, sys, loc.clone())?.not();

    let should_permute = match remaining {
        0 => {
            if needs_final_permute_if_empty {
                empty_input.or(&pos, loc.clone(), sys)
            } else {
                pos
            }
        }
        1 => {
            let (b, x) = &input[n - 1];
            let p = pos;
            let x_masked = x.mul(&b.to_field_var(), None, loc.clone(), sys)?;
            add_in(sys, loc.clone(), state, &p, &x_masked)?;
            if needs_final_permute_if_empty {
                Boolean::any(&[&p, b, &empty_input], sys, loc.clone())?
            } else {
                Boolean::any(&[&p, b], sys, loc.clone())?
            }
        }
        _ => unreachable!(),
    };

    cond_permute(sys, loc, &should_permute, state)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        poseidon::{ArithmeticSponge, Sponge},
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    /// 5 flagged inputs; flags fixed by the test matrix.
    const N: usize = 5;

    struct OptSpongeCircuit {
        flags: [bool; N],
    }

    impl SnarkyCircuit for OptSpongeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        type PrivateInput = [Fp; N];
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mut sponge = OptSponge::new();
            for i in 0..N {
                let x: FieldVar<Fp> = sys.compute(loc!(), move |_| private.unwrap()[i])?;
                let b: Boolean<Fp> =
                    sys.compute(loc!(), move |_| private.unwrap()[i] != Fp::from(0u64))?;
                // use the actual test flag as the witness of the boolean
                let _ = b;
                let flag: Boolean<Fp> = {
                    let f = self.flags[i];
                    sys.compute(loc!(), move |_| f)?
                };
                sponge.absorb((flag, x));
            }
            sponge.squeeze(sys, loc!())
        }
    }

    /// With the given flags, the opt sponge must hash exactly the flagged
    /// values, like a plain out-of-circuit sponge absorbing them.
    #[test]
    fn opt_sponge_matches_plain_sponge() {
        let mut rng = o1_utils::tests::make_test_rng(None);

        for flags in [
            [true; N],
            [true, false, true, false, true],
            [false, true, true, false, false],
            [false; N],
        ] {
            let circuit = OptSpongeCircuit { flags };
            let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

            use ark_ff::UniformRand;
            let values: [Fp; N] = std::array::from_fn(|_| Fp::rand(&mut rng));

            // out-of-circuit reference: a plain sponge absorbing the flagged values
            let mut reference =
                ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>::new(
                    Vesta::sponge_params(),
                );
            for (i, v) in values.iter().enumerate() {
                if flags[i] {
                    reference.absorb(&[*v]);
                }
            }
            let expected = reference.squeeze();

            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), values, true)
                .unwrap();

            assert_eq!(*public_output, expected, "flags = {flags:?}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}
