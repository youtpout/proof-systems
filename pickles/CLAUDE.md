# Port de Pickles (OCaml → Rust) — branche `pickle-rs`

Référence OCaml : `~/Projects/mina/src/lib/crypto/pickles` (49 modules).
Socle : le crate `snarky` (DSL + constraint system, parité de gates validée
contre l'OCaml) ; consommateur cible : o1js (branche `pickle-rust`,
voir `o1js/RUST_MIGRATION.md`).

Méthode éprouvée sur snarky : porter module par module, avec à chaque étape
un test de parité contre l'implémentation kimchi/OCaml existante.

## Handoff actuel — parité VK o1js

Dernier jalon : commit `9aba71a8f5` (`Port o1js Pickles dummy constraints`).
Le préambule `dummy_constraints()` injecté par le binding OCaml d'o1js est
maintenant porté côté Rust dans `api.rs::o1js_dummy_constraints`.

État vérifié avec `o1js/src/tests/rust-pickles-step-gates-diff.ts` :

- **STEP CIRCUIT : FULL MATCH (0 divergence)** — 512 rows, gates, coefficients
  et wiring de permutation identiques au step jsoo sur la méthode minimale.
- Correctifs qui ont fermé les 10 dernières divergences :
  - `snarky/gadgets/curve.rs::assert_on_curve` : Square(x,x²) + R1CS(x³) +
    Square(y, x³+b) comme OCaml (au lieu de mul/R1CS partout) ;
  - `curve.rs::add_complete` : ordre d'exists OCaml add_fast (same_x, inf_z,
    x21_inv, s, x3, y3) et `inf = constante zéro` (check_finite) — la
    constante rejoint la classe de permutation du zéro caché ;
  - `scalar_challenge.rs::endo` : seal de `endo·xt` (émet `[E,-1]` en l/r
    comme le Utils.seal OCaml) et ordre d'addition `t + phi_t` ;
  - `constraint_system.rs::EcEndoscalar` : réduction des champs du round en
    ordre inverse (x7→n0), l'ordre d'évaluation droite-à-gauche des records
    OCaml ;
  - les cycles de permutation OCaml sont TRIÉS par (row, col) avant rotation
    (`equivalence_classes_to_hashtbl`) — le nôtre aussi, vérifié.

**WRAP : outillage en place, premier diff obtenu** (`b205238bd7`) :
`fq_prover_to_json` (kimchi-wasm, aussi dans le submodule mina d'o1js —
wasm bundlé rebuilé), `prove_base_case_with_wrap_dump` +
`dump_recorded_wrap_circuit` (two-pass) + NAPI, et
`o1js/src/tests/rust-pickles-wrap-gates-diff.ts` (intercept wrap-pk).

Premier état (méthode minimale) : 8192 rows des deux côtés mais divergence
STRUCTURELLE (pas un simple problème d'ordre) :
- public input **40 vs 31** : le statement wrap jsoo porte 9 slots de plus
  (hypothèse : les 8 feature flags + joint_combiner — vérifier
  `composition_types` OCaml `Wrap.Statement.to_data`/spec) ;
- Poseidon **1001 vs 671**, EndoMulScalar **184 vs 0** (jsoo convertit les
  scalar challenges in-circuit via le gate, nous précalculons),
  EndoMul 2464 vs 2016, Generic 569 vs **3764** (notre packing émet
  beaucoup plus de generic).
**Phases A+B FAITES** (`ec2d4dab93`, `f952e167be`) : SRS pleins partout
(step 2^16 / wrap 2^15 — 16/15 rounds IPA fixes, dispatch 9-16 supprimé,
chaîne stable re-threadée step≠wrap rounds, verify.rs en SRS Tock) et
statement wrap = layout OCaml 40 slots (13+ROUNDS+11, flags booléens
contraints, joint combiner à zéro, mina_bin_prot en 24+16). Suites : 9/9
recorded, 101/101 lib.

État du diff wrap après A+B (méthode minimale) :
- public input **40 = 40** ✓ ; CompleteAdd **258 = 258** ✓ ;
  VarBaseMul **663 = 663** ✓ ; EndoMul **2464 = 2464** ✓ — toute la
  partie EC du wrap est exacte en comptage.
- Restent : **Generic 5594 vs 569** (≈10× — notre arithmétique déférée
  finalize/ft_eval/b émet du generic brut là où OCaml est plus compact),
  **EndoMulScalar 0 vs 184** (= 23 conversions to_field_checked de 8 rows :
  OCaml convertit les scalar challenges in-circuit via le gate — porter
  `scalar_to_field` de scalar_challenge.rs dans le chemin wrap),
  **Poseidon 825 vs 1001** (176 rows = 16 blocs : absorb/opt-sponge),
  et le domaine : notre wrap déborde à 2^14 (16384 rows) vs 2^13 jsoo —
  il repassera sous 2^13 en résorbant l'excès de Generic.
État du diff wrap (méthode minimale) — **5/7 gate types EXACTS** :
- 8192=8192 rows, CompleteAdd 258, VarBaseMul 663, EndoMul 2464,
  EndoMulScalar 184, **Poseidon 1001=1001** tous exacts ;
- reste **Generic 450 vs 569** (−119) et l'ordre (type=2795 rows
  déplacées, coeffs=764, wiring=373).

Correctifs additionnels de cette session (au-delà du handoff précédent) :
- `Wrap_hack.pad_accumulator` : le step de base porte 2 accumulateurs
  dummy (kimchi `prev_challenges`, sg over full Tick SRS) ; le wrap
  absorbe/masque les 2 sg_old ; le finalize récursif distingue
  `finalize_prev_challenges` (padded, Fr-sponge) de `prev_challenges`
  (unpadded, digest) — commit `Pad step-proof accumulators`.
- Codex : masque optionnel des sg_old, packing du statement différé dans
  l'IVP (`public_input.rs` : `scale_fast2_prime`/`split_field`/correction
  Lagrange), seal des champs, consistance des feature flags,
  ordonnancement du witness wrap.
- `Wrap.Other_field.check` : les 5 slots fp du statement sont contraints
  ≠ des `forbidden_shifted_values` (patterns 255-bit ambigus mod Fp,
  filtrés aux représentables en Fq) — `shifted_value::forbidden_shifted_values_fq`.

**Dernier écart Generic — origine localisée : `x_hat` / public input wrap.**
État actuel après `Flush wrap generic gates before custom rows` :
- rows/public input : **8192=8192**, **40=40** ;
- compteurs exacts hors Generic/Zero : Poseidon 1001, CompleteAdd 258,
  VarBaseMul 663, EndoMulScalar 184, EndoMul 2464 ;
- reste **Generic 508 vs 569** et **Zero 3114 vs 3053**.

Pistes testées et écartées :
1. VK step + `h` en constantes → 450→421 (PIRE, jsoo witnesse la VK),
   reverté ;
2. seal des entrées d'`add_fast` → no-op (`add_complete` réduisait déjà) ;
3. **swap `OptSponge` dans l'IVP → NO-OP** : avec les flags à `true`
   constant, la machinerie conditionnelle (`add_in`, masque) se replie
   (mul par constante 1 = 0 contrainte), Generic reste à 450. Donc
   l'opt-sponge N'est PAS la cause (contrairement à ce que le motif
   laissait croire) ;
4. réduction complète de l'état `EcScale` avant émission des rows, comme le
   backend OCaml → no-op mesurable ;
5. `combine_commitments` avec préfixe `sg_old` optionnel (`Opt.Maybe`) →
   casse la parité structurelle EC (EndoMul +64, CompleteAdd +6), reverté ;
6. flush des generic sur changement de label/loc → overshoot Generic 617,
   EC/Poseidon inchangés mais mauvais pour l'iso, reverté.

Localisation mécanique :
- les premières rows manquantes `jsoo Generic / rust Zero` sont
  `701,703,705,709,723,725,727,741,743,745,759,761` ;
- elles tombent dans le premier `scale_fast` de `x_hat`, juste après le
  `split_field` de `scale_fast2_prime` :
  - row Rust 657 : `scale_fast2_prime split` (`assert equals` +
    `split_field: odd bit`) ;
  - rows Rust 660–761 : `scale_fast` ;
  - puis `EC complete add` / `if_`.
- labels des rows manquantes : 24 `scale_fast`, 12 `Poseidon`, 2 `endo`,
  9 padding/final rows sans label ; la première grosse zone est donc le
  commitment du public input (`x_hat`), pas `ft_comm`, pas
  `combine_commitments`, pas Poseidon lui-même.

Motifs manquants côté jsoo mais absents ou sous-représentés côté Rust :
- `E,1,E,0,0` (27 demi-lignes, **0** côté Rust) ;
- `0,0,E,0,0` (9, **0** côté Rust) ;
- `0,0,1,0,0` (9, **0** côté Rust) ;
- `1,0,E,0,0` (8, **0** côté Rust).

Conclusion : l'écart vient du chemin OCaml
`wrap_verifier.ml::{lagrange_with_correction, x_hat fold, Ops.scale_fast2'}`
vs Rust `public_input.rs::{statement_terms, public_input_commitment}` +
`plonk_curve_ops.rs::{scale_fast2_prime, scale_fast2, scale_fast_unpack}`.
La prochaine correction doit porter fidèlement les seals/réductions et
corrections Lagrange de ce chemin, en particulier autour du fold
`Add_with_correction ((x, num_bits), chunks)` et de `scale_fast2_prime`.

État committé : Generic 508 vs 569, 6/7 gate types exacts, 9/9 recorded.
Dumps : `/tmp/claude-1000/wrap-circuit-{jsoo,rust}.json`.
