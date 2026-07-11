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

**Dernier gros écart Generic (−119)** localisé : région rows ~700-1206,
motif `*,*,*,0,0,-1,1,-1,0,0` × 139 chez jsoo, absent chez nous. C'est
le packing du statement de l'étape vérifiée dans `x_hat`
(`pack_statement` OCaml → `split_field` par slot 255-bit → term Packed +
Cond). Notre `XHatInput::Statement` pour le wrap de base ne passe qu'un
slot (le digest) : il faut router les 40 slots du statement step à
travers `statement_terms` avec les Lagrange correspondants. Ensuite :
passe d'ORDRE d'émission (comme la phase step) puis coeffs/wiring.

Correctifs de la session (commits `5a50fd40`→) :
- `challenge.rs::lowest_128_bits` : range-check des moitiés 128-bit via
  `to_field_checked` (gate EndoMulScalar, 8 rows) au lieu de 128 booléens
  unpack (≈ −3000 Generic) ; split `squeeze_scalar` (hi seul) vs
  `squeeze_challenge` (hi+lo) — alpha/zeta/prechallenges/c en scalar ;
- digest de la VK step **calculé in-circuit** (28 points, ordre
  VerifierIndex::digest) au lieu de témoigné ;
- `hash_messages_for_next_wrap_proof` reprend le sponge d'un état
  CONSTANT pré-calculé (Wrap_hack) : préfixe dummy hors-circuit,
  `DuplexState::from_constant_state` ajouté à snarky ;
- tous les points witnessés du wrap passent `assert_on_curve`
  (exists Inner_curve.typ).

Pistes précises pour les derniers écarts (localisation par déciles) :
1. **Generic −91 dans rows 820-1640** : le packing du statement step dans
   l'IVP — OCaml `pack_statement`/`split_field` découpe chaque slot
   255-bit en (Field, Boolean) avec seal + assert de recomposition
   (patterns `E3fff` ≈ 2^254 dans le dump) ; nos step_statement_terms
   n'émettent pas ces découpes.
2. **Generic/Zero restants** : les histogrammes montrent uniquement
   Generic −162 / Zero +162 côté Rust. Les segments de diff sont dispersés
   (ordre d'émission du transcript, opt-sponge simulé, petits asserts de
   packing), donc ne pas ajouter de dummy constraints aveugles : faire la
   passe coeffs/wiring comme pour le step.
3. Ensuite : passe coeffs/wiring comme pour le step (ordre d'émission,
   union des constantes, tri des cycles) — même méthodologie éprouvée.


**Session parité wrap — faits vérifiés & gotchas** :
- Layout du statement wrap o1js = **40 slots** (décodé depuis le spec OCaml,
  `composition_types.ml In_circuit.spec` + `Spec.pack`) : 5 fp (Type1, 1 slot
  chacun) + 2 challenges + 3 scalar challenges + 3 digests + **16 bp
  challenges** + 1 branch_data + **8 feature flags publics** (o1js compile en
  `Maybe`) + **2 slots joint_combiner opt**. Builder :
  `wrap_statement_to_field_elements_ocaml` (40 slots, non branché).
- **Cause racine des 16 bp challenges** : Mina prouve sur des SRS pleins
  (2^16 step / 2^15 wrap) — les rounds IPA ne dépendent PAS du domaine.
  Notre pipeline dimensionne le SRS au domaine (rounds = log2(domaine)).
  Opt-in ajouté : `compile_to_indexes_with_domain_and_srs(min_domain,
  Some(srs_log2))`. Le branchement (ROUNDS fixes partout, plus de dispatch
  9-16) est LE prérequis du wrap iso.
- `rust_pickles_decode_mina_proof_base64` décode un proof side-loaded
  jsoo/Mina (o1js `proof.toJSON().proof`). Sur le dummy proof o1js
  (`dummyBase64Proof`) : échec `NonCanonicalField(0)` → **notre codec V3 lit
  le statement en Fq mais Mina stocke les 5 valeurs différées en Fp (Tick),
  qui peuvent dépasser le modulus Fq** — le codec doit typer les slots
  champ par champ. À corriger avant tout round-trip réseau.
- **GOTCHA rebuild wasm bundlé o1js** : le bc.cjs (jsoo OCaml) passe les
  gate types par INDICE numérique ; la révision du proof-systems imbriqué
  doit exposer les variants Cairo dans `GateType` (`6c3f61dd1e` "Expose
  Cairo gate type ABI variants") sinon les indices décalent et le prove
  jsoo échoue en "division by vanishing polynomial". Le wasm actuel est
  buildé depuis `6c3f61dd1e` + fq_prover_to_json (`866c3ab277`). NB : le
  prove jsoo échoue encore sur cette branche (peut-être cassé avant nous —
  c'était le premier prove jsoo tenté) ; le compile jsoo (dumps de gates,
  VK) fonctionne. Le rebuild complet des bindings (`build:bindings-node`)
  échoue sur les crates vendorées (kimchi-stubs-vendors vs o1-utils 0.7.0).
- **Ground truth VALIDÉ sur le dummy proof o1js** (sexp parsé) : le
  statement réseau est MINIMAL — deferred_values = {plonk(alpha, beta,
  gamma, zeta, joint_combiner, feature_flags), **16 bp challenges**,
  branch_data} SANS cip/b/xi (re-dérivés du prev_evals) ; wrap IPA =
  **15 rounds** (SRS Tock 2^15 plein confirmé) ; messages_for_next_wrap
  porte 2 vecteurs de challenges. Décodeur structuré :
  `WrapProofBaseV3::from_mina_bin_prot` (miroir de to_mina_bin_prot,
  round-trip testé) + fallback dans le NAPI.
- **GOTCHA format o1js** : `proofToBase64` d'o1js = base64 d'un **SEXP
  ASCII** (`((statement((proof_state...`), PAS du bin_prot. Le bin_prot
  est le format réseau/GraphQL. Pour décoder des proofs o1js côté Rust il
  faudra un parseur sexp (ou convertir en JS).

## Carte de portage

| OCaml | Rust | Statut |
|---|---|---|
| `common.ml` (constantes) | `src/common.rs` | 🟨 constantes de base |
| `endo.ml` | `src/endo.rs` | ✅ (via KimchiCurve) |
| `tick_field_sponge.ml`, `tock_field_sponge.ml`, `make_sponge.ml` | `src/sponge.rs` | ✅ out-of-circuit (FieldSponge) ; le sponge in-circuit est `snarky::gadgets::sponge::DuplexState` **corrigé à la source** (bug : capacité remise à 0 chaque permutation → faux pour ≥3 inputs ; réécrit avec l'état 3 éléments d'ArithmeticSponge). `pickles::sponge::PoseidonSponge` = ré-export. Parité `DuplexState == ArithmeticSponge` (1/2/3/5/8 inputs × 3 squeezes) testée **dans snarky** |
| `scalar_challenge.ml` (out-of-circuit) | `src/scalar_challenge.rs` | ✅ **parité kimchi testée** |
| `scalar_challenge.ml` (in-circuit, endo gadget) | `src/scalar_challenge.rs::endo` | ✅ **parité testée** : `endo(T, chal)` == `[to_field(chal)]·T` (ark), preuve kimchi vérifiée (gate EndoMul, 32 rows) |
| `scalar_challenge.ml::to_field_checked` (in-circuit) | `src/scalar_challenge.rs::scalar_to_field` | ✅ **parité testée** : interprète un challenge 128-bit comme `a·endo + b` via le gate **EndoMulScalar** (8 nybbles/row, 8 rows), contraint `n == scalar` ; == `to_field` hors-circuit / kimchi, preuve vérifiée |
| `impls.ml` (Step/Wrap impls) | `src/tick_tock.rs` (trait Side) | 🟨 types posés ; relier aux RunState snarky |
| `plonk_curve_ops.ml` | `src/plonk_curve_ops.rs` | 🟨 `add_fast`, `scale_fast_msb_bits`, `scale_fast_unpack`, `scale_fast` ✅ **parité testée** (VarBaseMul, bits contraints par le gate + n_acc == scalar) ; `endo_inv` ✅ (dans scalar_challenge.rs) ; `scale_fast2` (Type2 odd/even) ✅ **parité testée** — plonk_curve_ops complet (hors `scale_fast2'` qui demande Other_field) |
| `opt_sponge.ml` | `src/opt_sponge.rs` | ✅ **parité testée** (4 motifs de flags == sponge de référence, preuves vérifiées) ; `recombine`/`of_sponge`/`consume_all_pending` à porter quand wrap_verifier en aura besoin ; `sponge_inputs.ml` ⬜ |
| `step_verifier.ml::finalize_other_proof` | ✅ **CŒUR ARITH ASSEMBLÉ in-circuit** (`src/finalize.rs::finalize_core`) — Fr-sponge (`src/fr_sponge.rs`) + scalar_to_field + ft_eval0 + combined_inner_product | **étapes 4-8 validées end-to-end** : `finalize_core` reconstruit le Fr-sponge (`squeeze_xi_r` : digest → prev_challenge_digest → ft_eval1 → public_evals[0]/[1] → absorb_evaluations z/selectors/w/coeffs/s), squeeze+check xi (`xi_correct` = compare 128-bit brut vs xi réclamé), convertit xi/r en champ via `scalar_to_field`, et reconstruit le combined inner product. **Test sur une vraie preuve** (avec ft_eval0 in-circuit) : `xi_field == oracles.v`, `r_field == oracles.u`, `cip == combined_inner_product`, `xi_correct == 1`. **`b_correct` (step 9) FAIT** : `finalize.rs::b_actual` reconstruit `b = h(ζ) + r·h(ζω)` in-circuit. **`plonk_checks_passed` FAIT** : découverte clé — `Plonk_checks.checked` ne vérifie qu'**UN seul** scalaire déféré, le scalaire de permutation `perm = -z(ζω)·β·α^21·zkp·∏_i(γ+β·s_i+w_i)` (les autres scalaires sont recalculés via la linéarisation/ft_eval0). Porté in-circuit : `ft_eval_circuit.rs::perm_scalar_circuit` (partage ScalarsEnvVar/EvalsVar avec ft_eval0), == `plonk_checks::perm_scalar` hors-circuit sur une vraie preuve. **LES 4 CONJONCTIONS de finalize_other_proof ont leur arith in-circuit** (xi_correct, combined_inner_product_correct, b_correct, plonk_checks_passed). **`finalize_all` + Shifted_value.Type2 FAITS** (`b9518652f0`, 22 tests) : `finalize.rs::finalize_all` assemble les 4 en `Boolean::all` (compare chaque valeur dérivée vs réclamée) ; `type2_shift`/`type2_to_field` (Type2 : to_field(repr)=repr+2^size_in_bits) pour lire les valeurs réclamées du statement ; testé accept (tout match → 1) + reject (chaque conjonction altérée → 0). **finalize_other_proof COMPLET au niveau fonction** (l'arith + l'assemblage boolean). Reste pour le brancher sur un VRAI statement pickles : types All_evals/chunked + deferred_values réels (nécessitent le prover step/wrap — pas encore porté, donc pas encore parity-testable end-to-end) ; feature flags (SkipIf/Not) pour gates optionnels (pas nécessaires en wrap : feature_flags=none). **Gotcha snarky** : une sortie publique qui est une lincomb négée (`x.scale(-1)`) ou un booléen (`Boolean::all`) doit être `.seal()`-ée sinon `DisconnectedWires` |
| `wrap_verifier.ml::incrementally_verify_proof` (oracles fq) | `src/oracles.rs` | 🟨 **dérivation des oracles fq in-circuit FAITE** (`7c4513ff97`) : `derive_fq_oracles` absorbe les commitments dans l'ordre exact de kimchi (vk_digest, public_comm, w_comm[15] → β, γ, z_comm → α endo, t_comm → ζ endo) via `absorb_commitment` (coords x,y = absorb_g). Comme un circuit step/Fp vérifie un wrap proof dont les commitments ont des coords Fp, le fq-sponge = même `PoseidonSponge`. Parité testée vs `ArithmeticSponge<Fp>` hors-circuit (même ordre absorb/squeeze). **`combine_commitments` FAIT** (`1f289e1065`, `bulletproof.rs`) : Horner `Σ xi^i·C_i` via le gate EndoMul (`acc = C_i + endo(acc, xi)`), parité ark testée (1/2/4 comms). **`bullet_reduce_terms` FAIT** (`83b1776931`) : partie EC de bullet_reduce, `Σ (endo_inv(L,pre) + endo(R,pre))`, parité ark testée (3 rounds). **`check_bulletproof_equation` FAIT** (`b1aa773dbf`, `bulletproof.rs`) : équation IPA finale `c·Q + δ == z1·(G + b·U) + z2·H` assemblée — `q = combined_polynomial + scale_fast(u,cip) + lr_prod`, `lhs = endo(q,c) + δ`, `rhs = scale_fast(cpc + scale_fast(u,b), z1) + scale_fast(H, z2)`, `equal_g = Boolean.all[x==,y==]`. Réutilise les bricks EC déjà portées (scale_fast Type1 `(2·repr+2^num_bits+1)·base`, endo, add_fast). Parité testée : δ choisi pour lhs==rhs (accept) et perturbé (reject). **`bullet_reduce_challenges` FAIT** (`b750c24f92`, `bulletproof.rs`) : la moitié sponge de bullet_reduce — par round IPA, absorb L puis R dans le transcript-sponge base-field puis squeeze un prechallenge 128-bit brut (`absorb_commitment` rendu `pub(crate)`). Parité testée vs `ArithmeticSponge<Fp>` (3 rounds). **`ft_comm` FAIT** (`85b3fbf2ad`, `commitments.rs`, IVC step 14) : commitment de la linéarisation `ft` = `perm·reduce_chunks(sigma_comm_last) + reduce_chunks(t_comm) - zeta_to_domain_size·reduce_chunks(t_comm)` ; `reduce_chunks` = Horner scale_fast par zeta_to_srs_length ; scalaires Type1. Parité in==out circuit (1 chunk sigma, 7 chunks t). **`ipa_challenges_transcript` FAIT** (`61a4b6c59b`, `bulletproof.rs`) : threading du sponge base-field dans l'ordre EXACT de kimchi (`poly-commitment/src/ipa.rs:371-383`, reproduit par pickles check_bulletproof) — `absorb_shifted(cip)` → `u = group_map(squeeze_field)` → prechallenges bullet_reduce → `absorb(δ)` → `c = squeeze_scalar`. Retourne `(u, prechallenges, c)` prêt pour `check_bulletproof_equation`. Parité vs mirror `ArithmeticSponge<Fp>` (2 rounds : u + 2 prechallenges + c tous OK). **Toutes les briques + le threading transcript de check_bulletproof sont FAITS et testés.** **derive_fq_oracles VALIDÉ CONTRE UNE VRAIE PREUVE PALLAS** (`802a5d9afd`) : β/γ reproduits == `proof.oracles()` kimchi sur de vraies commitments (coords Fp), pas juste un mirror synthétique — le cas cross-field step/wrap réel (circuit Fp absorbe une preuve Pallas). CONFIRMÉ (verifier.rs:1186) : le sponge fq de check_bulletproof est le MÊME que celui des oracles, continué. **Shifted_value Type1/Type2 + embed cross-field FAIT** (`ccc4fbd963`, `shifted_value.rs`) : `type1_to_field(t)=2t+2^size+1` (forme scale_fast), `of_field(s)=(s-2^size-1)/2` ; `embed_repr` Fq→Fp préserve l'entier (sound car modulus Fp > Fq). Testé : pipeline complet `s → of_field → embed → scale_fast(g,255) == s·g`. **Reste dans incrementally_verify_proof** : uniquement l'ASSEMBLAGE FINAL — construire la liste `without/with_degree_bound` (sg_old, x_hat, ft_comm, z_comm, sélecteurs, w_comms, sigmas) pour `combine_commitments`, brancher les scalaires déférés (cip/b/z1/z2 via shifted_value), et tester equal_g==true de bout en bout contre l'ouverture IPA d'une vraie preuve Pallas. Tout est débloqué (harness preuve Pallas + shifted_value cross-field prêts) |
| `step.ml`, `step_main.ml`, `step_branch_data.ml`, `step_main_inputs.ml` | `src/step_main.rs`, `src/step_verifier.rs`, `src/step_witness.rs`, `src/recursive_step.rs`, `src/api.rs` | 🟨 cœur step fonctionnel pour le cas de base + premier step récursif : `step_main` vérifie un wrap proof avec finalize + x_hat + IVP, `step_witness` rejoue le transcript wrap côté prover, `recursive_step::prepare_recursive_step` construit witness/statement/recursion challenge. `RecursiveStepCircuit` accepte un app main embarqué (`app: Option<EmbeddedAppMain>` type-erased, `prove_recursive_step_with_app`/`prove_first_recursive_cycle_with_real_vk_and_app`) : sa sortie devient l'app state lié par le digest du nouveau statement. **Parité gate-level vs jsoo EN COURS** : les 28 points wrap-VK sont contraints on-curve dans StepCircuit et le préambule `dummy_constraints()` o1js est porté (EndoMulScalar+CompleteAdd×3+VarBaseMul+EndoMul). État sur méthode minimale : 512 rows des deux côtés, public_input=1, histogrammes identiques (Generic 89, Poseidon 319, Zero 98, CompleteAdd 3, VarBaseMul 1, EndoMul 1, EndoMulScalar 1). Reste à aligner 10 wirings/coefficients internes du préambule dummy (`Scalar_challenge.to_field_checked'`, `Ops.scale_fast`, `Scalar_challenge.endo`) ; les commitments VK restent donc 0/28. Outils : `rust_pickles_recorded_step_circuit_json` (NAPI) + `src/tests/rust-pickles-step-gates-diff.ts` (o1js). Reste : généraliser aux règles inductives/multi-branches/multi-proofs, padding de preuves non vérifiées, API compile/prove propre |
| `wrap.ml`, `wrap_main.ml`, `wrap_main_inputs.ml`, `wrap_verifier.ml`, `wrap_domains.ml`, `wrap_hack.ml` | `src/wrap.rs`, `src/wrap_main.rs`, `src/api.rs` | 🟨 cœur wrap fonctionnel pour le wrap du cas de base : replay transcript step, statement packé, x_hat via Lagrange SRS, finalize Type2, vérification IPA et preuve wrap vérifiée. Reste : domaines Pickles paddés complets (16 rounds), vrai wrap VK via compilation 2-passes, enchaînement des wrap proofs après plusieurs steps |
| `composition_types.ml` (statement types), `bulletproof_challenge.ml`, `branch_data.ml`, `Features` | `src/composition_types.rs` | ✅ types de données quasi complets : Minimal plonk, DeferredValues, Unfinalized, wrap::ProofState/Statement, **MessagesForNextWrapProof (+to_field_elements testé), MessagesForNextStepProof, PlonkVerificationKeyEvals (7 sigma+15 coeff+6, to_list ordonné testé)** ; restent : Plonk.In_circuit (scalaires dérivés — en pratique calculés par finalize), Spec/typ (encodage circuit hlist) |
| `plonk_types.ml::All_evals` | `src/all_evals.rs` | ✅ **factor testé** : `AllEvals` (ft_eval1 + public_input + evals aux 2 points) sur les types kimchi ProofEvaluations/PointEvaluations ; `factor` sépare les evals appariées par point == evals bruts de la preuve ; `actual_evaluation_circuit` (combinaison Horner des chunks) dans ft_eval_circuit.rs, testé |
| `per_proof_witness.ml`, `reduced_messages_for_next_proof_over_same_field.ml` | `src/recursive_step.rs`, `src/step_witness.rs`, `src/hash_messages.rs`, `src/composition_types.rs` | 🟨 premier per-proof witness step porté et validé : evals step flattenées, x_hat lagranges, statement width-1, messages_for_next_step hash, `RecursionChallenge`. Reste : types/API génériques pour N preuves et règles inductives, reduced-messages same-field complet, padding/dummy proofs dans le flux général |
| `verification_key.ml`, `side_loaded_verification_key.ml` | ⬜ | VKs (side-loaded = compat o1js) |
| `proof.ml`, `verify.ml` | `src/verify.rs` | ✅ **vérification standalone side-loaded** : `verify_side_loaded(_with_step_vk)` reconstruit le VerifierIndex kimchi du wrap depuis les 28 commitments de la VK side-loaded (domaine, SRS, shifts, linéarisation sans gates optionnels, prev_challenges=0), vérifie le binding du digest messages-for-next-step (slot 12, app_state + accumulateurs + old challenges) puis la preuve kimchi — sans backend prover. Testé sur vraies preuves N0 et N1 (accept + reject : mauvais app_state, statement altéré, wire proof corrompu, arité de messages incohérente). Gotcha N1 : le digest lie la wrap VK du programme (dlog_plonk_index), pas forcément la VK side-loaded du proof — d'où la variante `_with_step_vk`. Décodage structurel des VK side-loaded exposé en NAPI (`rust_pickles_decode_side_loaded_vk`, base58 réseau ou base64 o1js) — parité VK vs jsoo : métadonnées identiques, 0/28 commitments (attendu tant que la parité gate-level des circuits n'est pas atteinte) |
| `compile.ml`, `inductive_rule.ml`, `tag.ml`, `types_map.ml`, `requests.ml` | `src/inductive_rule.rs`, `src/api.rs`, `src/recorded.rs` | 🟨 `PicklesProgram`/`HeterogeneousPicklesProgram` + backends N0/N1/N2 (`BaseCaseRuleBackend`, `DirectN1/N2Backend`) ; **circuits enregistrés** (`recorded.rs`) : un `RecordedCircuit` JSON (lincoms + contraintes kimchi, format o1js) est rejoué comme `StepApp` et prouvé par le pipeline base-case (domaine mesuré → dispatch monomorphisé rounds 9-16). Exposé en NAPI (`rust_pickles_prove_recorded_base`/`verify_side_loaded`) et WASM (`kimchi-wasm/src/pickles.rs`). Testé e2e prove+verify standalone. `prove_recorded_n1` : base + un cycle récursif N1 complet depuis JS (envelope avec accumulateur/challenges/dlog index pour verify standalone), exposé NAPI+WASM, testé e2e. **Chaînage SelfProof FAIT** : `prove_recorded_base_case_keep` garde le `BaseCaseProof` complet dans un `RecordedBaseHandle` opaque (enum rounds 9-16) ; `prove_recorded_n1_over(handle, circuit, witness)` prouve un cycle N1 dont le step **exécute un nouveau circuit** (app main embarqué type-erased dans `RecursiveStepCircuit.app`) en vérifiant la preuve gardée — le digest lie le nouvel app state. Exposé NAPI (`External`) + WASM (`WasmRecordedBaseHandle`), testé e2e (Rust + o1js 9.4s). Limites : step+app doit tenir en 2^14 (panique sinon), handle non sérialisable inter-process. Reste : recorded N2. RecordedConstraint couvre TOUTE la surface KimchiConstraint (basic, generic, poseidon, ec_add_complete, ec_scale, ec_endoscale, ec_endoscalar, range_check/0/1, lookup) — EcAddComplete testé e2e (preuve Pallas add + verify standalone) |
| `cache.ml`, `cache_handle.ml`, `dirty.ml`, `proof_cache.ml` | ⬜ | caches de clés (basse priorité) |
| `challenge_polynomial` (wrap_verifier.ml G) + `Ipa.compute_challenge(s)` (common.ml) + `combined_inner_product` (finalize_other_proof step 11) | `src/ipa.rs` | ✅ **parités testées** : challenge_polynomial in/out-circuit sur prechallenges réels ; `combined_inner_product` (reconstruction `es` en ordre kimchi, alimentée par NOTRE ft_eval0) == `OraclesResult.combined_inner_product` kimchi sur une vraie preuve (cas base, sans gates optionnels ni lookup) ; **version in-circuit `combined_inner_product_circuit` aussi validée** (Σ xi^i·(zeta+r·zetaw), alimentée par notre ft_eval0, preuve vérifiée) |
| **`ft_eval0` in-circuit** (+ scalars_env in-circuit) | `src/ft_eval_circuit.rs` | ✅ **parité testée + preuve** : ft_eval0 calculé entièrement en circuit (scalars_env FieldVar : alpha_pows/zk_poly/ζ powers ; constant_term via eval_polish ; arithmétique de permutation) == `OraclesResult.ft_eval0` kimchi sur une vraie preuve |
| **Évaluateur `PolishToken` in-circuit** | `src/expr_eval.rs` | ✅ **parité testée + preuve** : notre stack machine sur `FieldVar` évalue le `constant_term` de la linéarisation kimchi == valeur `PolishToken::evaluate` hors-circuit, sur une vraie preuve, tous inputs témoignés. vanishes_on_last_n_rows + unnormalized_lagrange_basis calculés in-circuit depuis ζ (via `div_var`). Reste : tokens feature-flag (SkipIf/Not) pour les gates optionnels |
| `plonk_checks.ml` (hors-circuit) | `src/plonk_checks.rs` | 🟨 scalars_env (zk_polynomial, alpha_pows 71, ω^{-zk}, ζ powers), `perm_scalar` (perm_alpha0=21) et `ft_eval0` portés ; **parité validée contre `kimchi::verifier::OraclesResult.ft_eval0` sur une vraie preuve** (vrais oracles Fiat-Shamir, evals combinées, constant_term via PolishToken ; zk_polynomial == permutation_vanishing_polynomial kimchi) ; le constant_term arrive en paramètre — en Rust il s'évaluera via `PolishToken`/`ExprOps` de kimchi (pas besoin du scalars.ml généré, y compris in-circuit si FieldVar impl ExprOps) |
| `util.ml::lowest_128_bits` / `squeeze_challenge` (step 8) | `src/challenge.rs` | ✅ **testé + preuve** : lowest_128_bits == référence hors-circuit ; **squeeze_challenge (sur PoseidonSponge fidèle) == référence hors-circuit** (ArithmeticSponge squeeze puis lowest_128) — parité du step sponge RÉSOLUE |
| `dummy.ml`, `ro.ml`, `commitment_lengths.ml`, `evaluation_lengths.ml`, `fix_domains.ml`, `timer.ml` | ⬜ | utilitaires au fil du besoin |

## Ordre de bataille proposé

1. **Fondations vérifiables** : scalar_challenge in-circuit (EndoMul),
   plonk_curve_ops, opt_sponge — chacun avec parité contre l'OCaml/kimchi.
2. **Types récursifs** : unfinalized, per_proof_witness, statements
   (types.ml de composition-types dans `pickles_types` OCaml — vérifier ce
   qui vit dans `mina/src/lib/pickles_types`).
3. **wrap_verifier puis step_verifier** (les circuits de vérification
   in-circuit — le gros du code).
4. **compile/prove/verify** : l'API, avec un ZkProgram jouet 2-branches
   comme critère de bout en bout (parité de VK avec l'OCaml).
5. Side-loaded keys (compat o1js SmartContract).

## Repères

- `snarky::gadgets` fournit déjà : poseidon/duplex, curve (add complet,
  double, scale naïf), group_map, bits/compare. Le scale devra passer aux
  gates VarBaseMul/EndoMul pour la parité de layout avec pickles.
- Les rounds IPA : Tick 16, Tock 15 (`common.rs`).
- Attention aux types OCaml `pickles_types` (vecteurs à taille typée,
  plonk_types) : en Rust, const generics.


## État (2026-07-08) — E2E CAS DE BASE ATTEINT 🏆

`pickles/tests/e2e.rs::pickles_base_case_end_to_end` **passe** via `src/api.rs::prove_base_case` :
StepCircuit (Vesta, app + digest accumulateur in-circuit) → preuve step →
`wrap::wrap_witness` (replay transcript complet, parité kimchi) →
statement wrap packé (`composition_types::wrap`) → WrapCircuit (Pallas,
`wrap_main::wrap_main` : x_hat sur le vrai Lagrange SRS, re-dérivation
Fiat-Shamir totale, asserts inconditionnels des deferred values, **équation
bulletproof assertée**) → preuve wrap vérifiée. 56 tests lib + e2e.

Côté circuit tout est assemblé : `step_main` (boucle `verify_one` =
finalize_deferred + hash_messages + verify{x_hat+IVP}) et `wrap_main`
(finalize Type2 par unfinalized + step_statement_terms avec split_field +
verify + asserts d'accumulateurs). Deux découvertes structurantes cette
étape (voir commits `4aa9bc856d`, `e77bb687d6`) :

1. **La linéarisation berkeley kimchi a zéro `index_terms`** → le split
   f_comm == celui de pickles → `equal_g` validé contre une vraie preuve
   kimchi (test `incrementally_verify_proof_accepts_real_kimchi_proof`).
2. **Fq (Tock) > Fp (Tick)** → côté step les scalaires déférés sont des
   **paires Type2** `(s_div_2, s_odd)` (kimchi `shift_scalar` branche
   `x - 2^255` + `absorb_fr` splitté) ; côté wrap des Type1 simples.
   → `plonk_curve_ops::ShiftedScalar{Type1, Type2}` avec `.absorb()`/`.scale()`.

Reste (tâche #15) : généraliser la récursion au-delà du premier step
récursif, domaines paddés 16 rounds + vrai wrap VK (compile 2-passes),
padding des preuves non vérifiées/dummy accumulators, reduced messages
same-field, API compile/prove pour plusieurs règles inductives, parité Ro
exacte + cross-vérification mina. Détail complet dans le memory tracker de
session (`snarky-rust-port.md`).

### Mise à jour : RÉCURSION VALIDÉE

`tests/recursion.rs::pickles_recursive_step` **passe** : un second step
circuit exécute `step_main` sur la preuve wrap du cas de base avec
`must_verify = true` — finalize réel des valeurs déférées du wrap statement
(scalaires Type1 du step proof #1, vraies évaluations), re-dérivation
complète du transcript du wrap proof (advice Type2 via `step_witness`),
recommitment du wrap statement par le vrai Lagrange Pallas (23 slots packés
+ 8 flags), équation bulletproof assertée, digest accumulateur exact.
**Le cycle récursif step→wrap→step fonctionne intégralement en Rust.**
Subtilité d'accumulateur élucidée : `messages_for_next_step_proof` paire
(sg du wrap proof, challenges du finalize = ceux du step proof) ; la
vérification de sg_wrap passe par l'Unfinalized du statement suivant.

La plomberie prover du premier step récursif est maintenant dans
`recursive_step::prepare_recursive_step` : construction du witness
`RecursiveStepData`, du statement width-1 et du `RecursionChallenge`. Le
layout statement est isolé dans `build_width1_step_statement` et les sous
étapes sont découpées (`flatten_proof_evaluations`, `wrap_x_hat_lagranges`,
`statement_challenges_to_field`, `recursion_challenge`). Le test
`pickles_recursive_step` ne conserve que le cas d'intégration
preuve/vérification.

### Mise à jour : API DU PREMIER STEP RÉCURSIF

`recursive_step::prove_recursive_step` expose maintenant l'étape complète
`prepare_recursive_step → compile RecursiveStepCircuit → prove_with_recursion
→ verify` comme primitive réutilisable. Le test `pickles_recursive_step`
consomme cette API au lieu de réassembler le prover manuellement, ce qui
déplace la plomberie du harness vers le crate et prépare le chaînage N>1 :
le résultat `RecursiveStepProof` conserve le statement width-1, la preuve
Vesta et son verifier wrapper, prêts pour la future étape de wrap générique
des step proofs récursifs.

### Mise à jour : WRAP STATEMENT GÉNÉRIQUE

`api::WrapCircuit` ne suppose plus que le step proof enveloppé a un unique
public input digest : `WrapWitnessData` porte maintenant une liste
`WrapStepStatementSlot::{Packed,Bool}` avec les Lagrange slots associés, et
`wrap_main::step_statement_terms` commite cette liste générique. Le cas base
reste le slot unique `Packed(digest,255)`.

`recursive_step::width1_step_statement_slots` encode le statement width-1 dans
le layout attendu pour le futur wrap récursif : 5 paires Type2
`Packed(255)+Bool`, digest `Packed(255)`, beta/gamma/alpha/zeta/xi et les
prechallenges en `Packed(128)`, `should_finalize` en bool, puis les deux
digests finaux en `Packed(255)`. Test de layout ajouté. Prochaine étape :
construire le `WrapWitnessData` d'un `RecursiveStepProof` et brancher
l'unfinalized réel dans `wrap_main`.

### Mise à jour : UNFINALIZED CÔTÉ WRAP

`api::WrapWitnessData` porte maintenant `unfinalized:
Vec<WrapUnfinalizedWitnessData>` et `WrapCircuit` construit les
`wrap_main::PerUnfinalized` réels : params de finalisation Type2, évaluations,
challenges raw, représentants Type2, anciens challenges/sg et dummies
`Wrap_hack`. Le cas base continue à passer avec `unfinalized=[]`.

`recursive_step::wrap_unfinalized_from_base` prépare l'unfinalized exact de la
preuve wrap du cas base, en rejouant les oracles Pallas, `step_witness`, les
evals, le `perm` et les dummies. Le test récursif vérifie désormais que cet
unfinalized reconstruit bien `base.statement[11]`
(`messages_for_next_wrap_proof`). Prochaine étape concrète : construire le
`WrapWitnessData` complet d'un `RecursiveStepProof` avec cet unfinalized, puis
prouver le wrap récursif.

### Mise à jour : TÉMOIN WRAP DU STEP RÉCURSIF

`recursive_step::prepare_recursive_wrap` assemble maintenant le
`WrapWitnessData` complet pour envelopper un `RecursiveStepProof` : public
input commitment du statement width-1, `wrap_witness` du step proof avec le
`sg_old` de récursion, `ProofsVerified::N1`, nouveau
`messages_for_next_wrap_proof`, Lagrange slots du statement générique, et
l'unfinalized préparé depuis le base wrap proof. Point important découvert :
le step récursif vérifie un wrap proof à 13 rounds, mais sa propre preuve
Vesta compile ici à 14 rounds ; les const generics sont donc séparées
(`VERIFIED_WRAP_ROUNDS` vs `STEP_PROOF_ROUNDS`). Le test récursif valide la
forme du statement wrap préparé et la présence de l'unfinalized. Prochaine
étape : appeler `WrapCircuit::<STEP_PROOF_ROUNDS, WRAP_STMT_LEN>` avec ce
témoin et résoudre les éventuels écarts de transcript/finalize en circuit.

`prepare_recursive_wrap` reconstruit désormais le commitment public `x_hat`
du statement step récursif depuis les slots width-1 et les Lagranges SRS, puis
l'asserte contre `public_comm.chunks[0]` produit par kimchi. Cette piste est
donc validée hors-circuit. Correction importante ensuite : le replay Fr-sponge
de `xi` pour le step proof récursif doit absorber le digest des
`prev_challenges` (`proof.prev_challenges[*].chals`) comme
`kimchi::verifier`, pas le digest vide du cas base. Le test récursif valide
maintenant aussi l'équation IPA hors-circuit reconstruite depuis
`PreparedRecursiveWrap` (`sg_old`, x_hat, ft, transcript IPA, `z1/z2`, `b`,
`cip`).

Le premier wrap récursif compile, prouve et vérifie désormais complètement.
Des labels d'assertion dans `wrap_main` ont isolé le dernier échec dans
`finalize_deferred`. La cause était le placement des challenges de padding :
un base step proof n'a aucun vrai `prev_challenges` à absorber pendant sa
finalisation, donc `old_bulletproof_challenges` doit être vide. Les challenges
factices restent nécessaires uniquement dans `hash_dummy_challenges` pour le
digest `Wrap_hack`. `prove_recursive_wrap` expose maintenant cette étape et le
test couvre le pipeline base step/wrap -> step récursif -> équation IPA
préparée -> wrap récursif prouvé et vérifié.

`recursive_step::prove_first_recursive_cycle` expose maintenant ce pipeline
step récursif → wrap récursif comme une seule primitive réutilisable et
retourne les deux preuves (la preuve step reste nécessaire à la finalisation
du cycle suivant). Le test de récursion consomme cette API au lieu
d'orchestrer séparément la préparation et les deux preuves.

La préparation N>1 est maintenant extraite :
`prepare_next_recursive_step` consomme les preuves step et wrap d'un
`RecursiveCycleProof`, utilise le statement public width-1 complet du step
précédent et conserve explicitement l'accumulateur wrap vérifié ainsi que les
challenges step finalisés. Le test construit le témoin de `step₃`.

La preuve de `step₃` a révélé puis permis de corriger une confusion :
`verify_one` utilisait une seule liste de commitments à la fois pour
reconstruire `messages_for_next_step_proof` et pour l'IPA du wrap. Ces deux
entrées sont maintenant séparées (`messages_for_next_step_accumulators` contre
`prev_challenge_polynomial_commitments`) et le digest N>1 est reconstruit
correctement. L'autre moitié de la réduction same-field est la conversion des
anciens prechallenges et l'évaluation de leurs challenge polynomials aux deux
points ; elle est maintenant intégrée au CIP de `finalize_deferred`.

### Mise à jour : BOUCLE RÉCURSIVE N>1

La finalisation différée inclut désormais les évaluations des anciens
challenge polynomials en préfixe du combined inner product. C'était la donnée
manquante à partir de `step₃` ; les quatre conjonctions de finalisation sont
exposées séparément pour diagnostiquer `xi`/CIP/`b`/permutation.

Les accumulateurs servant à `messages_for_next_step_proof` sont séparés des
commitments de récursion kimchi absorbés par l'IPA. La même séparation existe
côté wrap entre les challenges du Fr-sponge de la preuve finalisée et les
challenges du hash `messages_for_next_wrap_proof`.

`prove_next_recursive_cycle` enchaîne maintenant une itération complète
step→wrap depuis un `RecursiveCycleProof`. Le test couvre
base → step₂ → wrap₂ → step₃ → wrap₃, avec preuve et vérification locales à
chaque couche ; il exerce aussi une itération supplémentaire step₄ → wrap₄
pour valider que l'API est réellement répétable.

Après la transition initiale, le harness se stabilise à 14 rounds et aux mêmes
longueurs de statements. `prove_stable_recursive_cycles` exploite ce point fixe
et boucle sur un nombre arbitraire de cycles sans réécrire les paramètres
const-generic à chaque niveau.

Les types wire réduits `reduced_messages::{Step,Wrap}` et leurs opérations
`prepare` sont portés : le VK step est réinjecté depuis son ordre canonique de
28 commitments et les prechallenges sont convertis via l'endomorphisme. Le
pipeline récursif utilise ces préparations au lieu de conversions parallèles.

Le padding front vers `MAX_PROOFS_VERIFIED=2` est désormais appliqué aux
messages wrap récursifs : avec une preuve réelle, un vecteur dummy précède le
vecteur réel, tant dans le statement hors-circuit que dans le recalcul
`wrap_main::new accumulator digest`. La récursion multi-cycle passe avec ce
layout paddé.

La généralisation multi-preuves a commencé : `ProofsVerified::prefix_mask`
encode les masks paddés (`N0=[0,0]`, `N1=[0,1]`, `N2=[1,1]`),
`front_pad_proof_slots` matérialise les slots dummy/réels, et
`build_step_statement` encode désormais un nombre arbitraire d'Unfinalized
avant les deux digests communs. Le wrapper width-1 existant délègue à ce
builder générique.

### Mise à jour : STEP WIDTH-2 PROUVÉ

`RecursiveStepWidth2Circuit` porte deux `RecursiveStepData`, déclare
`PREV_CHALLENGES=2`, vérifie les deux slots wrap réels et contraint le digest
commun `messages_for_next_step_proof` sur les deux accumulateurs/challenge
vectors. `prepare_recursive_step_width2` assemble les deux segments
Unfinalized et les deux recursion challenges ; `prove_recursive_step_width2`
compile, prouve et vérifie le branch.

Le test `pickles_recursive_step_width2` passe avec deux slots réels et
désormais deux preuves de base distinctes. La construction
`RecursiveStepData → PerProofInput` est extraite et le circuit appelle
directement une seule fois `step_main(&[PerProofInput; 2])` : les deux preuves
partagent donc le VK et le sponge d'index, mais conservent leurs propres états
applicatifs précédents. L'état applicatif courant est fourni explicitement au
branch et alimente le calcul du digest final, comme dans le branch
multi-preuves Pickles.

### Mise à jour : WRAP WIDTH-2 PROUVÉ

La préparation wrap est désormais indépendante du wrapper width-1 : elle
consomme directement index, proof, statement, slots, liste d'Unfinalized et
anciens accumulateurs. `prepare_recursive_wrap_width2` fournit deux
Unfinalized, utilise les slots du statement width-2 et encode
`ProofsVerified::N2`. L'API width-2 reçoit les deux preuves de base et construit
deux témoins Unfinalized et deux anciens accumulateurs réellement distincts ;
elle ne duplique plus silencieusement le premier témoin.

Le test width-2 couvre maintenant le pipeline complet :
deux slots wrap réels distincts → preuve step récursive avec deux recursion challenges →
finalisation des deux anciens proofs dans `wrap_main` → équation IPA →
preuve wrap Pallas vérifiée.

### Mise à jour : DOMAINES PICKLES STABILISÉS

Snarky expose maintenant une compilation avec domaine minimal explicite. Elle
ajoute des portes zéro avant la construction de l'index tout en laissant le
témoin logique inchangé. Le pipeline width-2 l'utilise pour compiler le step
sur le domaine Tick `2^16` et le wrap sur le domaine Tock déterminé par
`ProofsVerified` (`2^13`, `2^14` ou `2^15`). Le `BranchData` publié encode ce
même domaine.

Le test width-2 vérifie désormais 16 challenges IPA sur la preuve step et
15 sur la preuve wrap. Cette stabilisation aligne la taille des accumulateurs
backend avec les challenges dummy protocolaires et débloque l'intégration
correcte d'un branch `N1` front-paddé.

### Mise à jour : ACCUMULATEURS PHYSIQUES SÉPARÉS

Le wrap ne dérive plus les `sg_old` backend depuis la liste logique des
`Unfinalized`. `WrapWitnessData` transporte maintenant explicitement les
accumulateurs physiques paddés, et `wrap_main`, le transcript ainsi que le
miroir IPA consomment tous cette même liste. Cette distinction est invisible
pour `N2`, mais nécessaire pour `N1` : le backend reste de largeur 2
(`[dummy, réel]`) tandis que la finalisation et les messages réduits ne
comptent qu'une preuve réelle.

### Mise à jour : PIPELINE N1 PHYSIQUEMENT PADDÉ

Le branch logique `N1` utilise maintenant réellement deux slots backend
`[dummy, réel]`. Le slot dummy est ignoré par `verify_one`, mais contribue au
message du step avec les challenges Step et le commitment Wrap canoniques de
`dummy.ml`. La preuve Kimchi plie séparément le commitment Step dummy. Le wrap
reçoit donc deux `sg_old` physiques tout en ne finalisant qu'un seul
`Unfinalized`, avec `ProofsVerified::N1`.

### Mise à jour : WRAP VK RÉELLE EN DEUX PASSES

`prove_base_case_two_pass` casse maintenant le cycle de compilation Pickles :
une passe bootstrap compile le wrap et en extrait les 28 commitments dans
l'ordre canonique, puis la passe finale reconstruit le step en hashant cette
VK réelle. Le wrap est recompilé et sa VK doit être strictement identique à
celle de la première passe avant que la preuve finale soit retournée.

Les helpers récursifs `*_with_real_vk` extraient ensuite automatiquement la
VK du wrap réellement vérifié. Le premier cycle refuse un base proof dont le
step n'aurait pas hashé cette même clé, ce qui ferme le chemin où une VK
factice pouvait encore être injectée entre le cas de base et la récursion.

### Mise à jour : MÉTADONNÉES DE RÈGLES INDUCTIVES

`inductive_rule` fournit maintenant des identifiants de règles stables, la
validation d'un programme multi-branches et le routage par règle. Chaque règle
fixe son arité `N0/N1/N2`, son domaine step, son domaine wrap dérivé et applique
le padding frontal des preuves. Les doublons, domaines Tick trop grands et
arités incohérentes sont rejetés avant toute compilation coûteuse.

`PicklesProgram::compile` attache désormais un `CompiledRuleBackend` concret à
chaque règle. `prove` route vers l'index lié au `RuleId` et retourne une preuve
taggée ; `verify` reprend ce tag et refuse les règles inconnues. Les backends
gardent leurs types de public input, witness, preuve et erreur, ce qui permet
aux circuits step/wrap de rester fortement typés sans effacement global.

`BaseCaseRuleBackend` raccorde cette abstraction au vrai pipeline Pickles
`N0`. Son `prove` exécute la compilation deux passes avec wrap VK réelle. Son
`verify` contrôle la VK embarquée, recalcule le digest depuis l'état
applicatif public, vérifie sa présence au slot canonique du wrap statement,
puis vérifie la preuve Kimchi. L'API générique n'est donc plus uniquement
validée par un backend synthétique.

Les branches récursives disposent maintenant de `N1RuleBackend` et
`N2RuleBackend`. Leur witness contient respectivement `[PreviousProof; 1]` ou
`[PreviousProof; 2]`, rendant une mauvaise arité non représentable. Avant
d'appeler le prover concret fourni par la branche, l'adapter construit les
slots Pickles `[dummy, réel]` ou `[réel, réel]`.

`DirectN1Backend` et `DirectN2Backend` raccordent maintenant directement ces
branches aux harnesses cryptographiques : préparation des anciens proofs,
preuve step récursive, preuve wrap, recalcul du digest public et vérification
Kimchi des deux couches. Aucune closure de proving n'est requise.

`HeterogeneousPicklesProgram` permet de réunir ces branches avec le backend
`N0` même lorsque leurs public inputs, witnesses et preuves Rust diffèrent.
L'effacement de types reste limité à la table de routage ; chaque appel
`prove`/`verify` redescend vers le type concret et retourne une erreur
explicite en cas de mauvais type, de règle absente ou de backend dupliqué.

### Mise à jour : VERIFICATION KEYS SIDE-LOADED

`SideLoadedVerificationKey` encapsule les 28 commitments canoniques et les
métadonnées de branche. La construction vérifie les domaines Tick/Tock,
l'accord `ProofsVerified`, le nombre de commitments, ainsi que l'appartenance
de chaque point à Pallas et à son sous-groupe. Une clé peut être extraite d'un
vrai index wrap puis convertie sans ambiguïté vers
`PlonkVerificationKeyEvals`.

La représentation circuit-facing suit maintenant exactement
`Pickles_base.Side_loaded_verification_key.to_input` : one-hot de
`max_proofs_verified`, one-hot de `actual_wrap_domain_size`, puis 28 points
dans l'ordre VK. Chaque coordonnée utilise un élément Pasta canonique
little-endian de 32 octets. Le décodeur rejette longueurs, champs non
canoniques, points invalides et métadonnées incohérentes.

Cette couche couvre la parité des field elements consommés par Pickles. Le
codec RPC Mina/bin_prot complet (versions Stable et enveloppes réseau) reste
distinct du payload circuit.

`mina_bin_prot::SideLoadedVerificationKeyV2` porte maintenant le sous-ensemble
exact nécessaire à la clé side-loaded : deux variants `Proofs_verified`, les
vecteurs fixes 7/15 avec leurs terminateurs `unit`, six commitments nommés,
champs Pasta canoniques et enveloppe Base58Check `0x1b`. La sortie du dummy
est comparée byte-for-byte (via son SHA-256 et sa longueur) au vecteur officiel
Mina.

La référence Mina officielle `6f65312c4caebc3cb0ef25f74ba7ea641c91b033`
a été auditée. Le vecteur officiel `test_ro.ml` pour
`bits_random_oracle("BitsRandomOracle")` est maintenant exécuté côté Rust.

`SideLoadedStepCircuit` consomme maintenant une clé side-loaded comme témoin
de taille fixe. Il contraint l'arité et les domaines à la règle compilée,
contraint les 28 commitments sur la courbe Pallas (dont le cofacteur vaut 1),
puis les injecte dans le hash `messages_for_next_step_proof`. Les tests
prouvent le cas valide et rejettent séparément un point et une arité altérés.

### Ce qu'il manque maintenant

- **Récursion N>1 / règles inductives** : transformer le harness
  `prove_base_case + prove_recursive_step` en API générique capable de
  chaîner plusieurs steps/wraps et plusieurs branches. La première brique
  d'API est maintenant portée et le commitment de statement générique côté
  wrap est prêt ; la plomberie `PerUnfinalized` côté wrap est branchée et le
  premier wrap d'un step proof width>0 est prouvé. Il reste à réinjecter ce
  wrap récursif dans le step suivant, puis à généraliser le bouclage
  step→wrap répété.
- **Vrai wrap VK récursif** : propager la compilation deux passes validée sur
  le cas de base aux règles récursives et à la future API multi-branches.
- **Padding Pickles complet** : généraliser le branch `N1` validé aux règles
  inductives et aux branches utilisateur, puis couvrir les autres données
  dummy (evals et statements) au-delà du chemin récursif actuel.
- **Parité Mina** : valider la sérialisation/RO/statement exacts contre Mina,
  pas seulement contre kimchi Rust et les mirrors locaux.
- **API utilisateur** : porter `compile.ml`, `inductive_rule.ml`, `tag.ml`,
  `types_map.ml` sous forme Rust idiomatique pour exposer un équivalent
  ZkProgram/prove/verify. La couche de métadonnées et validation des règles est
  en place ; il reste à lui attacher les closures de circuits et les index.
