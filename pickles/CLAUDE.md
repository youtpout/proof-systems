# Port de Pickles (OCaml → Rust) — branche `pickle-rs`

Référence OCaml : `~/Projects/mina/src/lib/crypto/pickles` (49 modules).
Socle : le crate `snarky` (DSL + constraint system, parité de gates validée
contre l'OCaml) ; consommateur cible : o1js (branche `pickle-rust`,
voir `o1js/RUST_MIGRATION.md`).

Méthode éprouvée sur snarky : porter module par module, avec à chaque étape
un test de parité contre l'implémentation kimchi/OCaml existante.

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
| `step.ml`, `step_main.ml`, `step_branch_data.ml`, `step_main_inputs.ml` | `src/step_main.rs`, `src/step_verifier.rs`, `src/step_witness.rs`, `src/recursive_step.rs`, `src/api.rs` | 🟨 cœur step fonctionnel pour le cas de base + premier step récursif : `step_main` vérifie un wrap proof avec finalize + x_hat + IVP, `step_witness` rejoue le transcript wrap côté prover, `recursive_step::prepare_recursive_step` construit witness/statement/recursion challenge. Reste : généraliser aux règles inductives/multi-branches/multi-proofs, padding de preuves non vérifiées, API compile/prove propre |
| `wrap.ml`, `wrap_main.ml`, `wrap_main_inputs.ml`, `wrap_verifier.ml`, `wrap_domains.ml`, `wrap_hack.ml` | `src/wrap.rs`, `src/wrap_main.rs`, `src/api.rs` | 🟨 cœur wrap fonctionnel pour le wrap du cas de base : replay transcript step, statement packé, x_hat via Lagrange SRS, finalize Type2, vérification IPA et preuve wrap vérifiée. Reste : domaines Pickles paddés complets (16 rounds), vrai wrap VK via compilation 2-passes, enchaînement des wrap proofs après plusieurs steps |
| `composition_types.ml` (statement types), `bulletproof_challenge.ml`, `branch_data.ml`, `Features` | `src/composition_types.rs` | ✅ types de données quasi complets : Minimal plonk, DeferredValues, Unfinalized, wrap::ProofState/Statement, **MessagesForNextWrapProof (+to_field_elements testé), MessagesForNextStepProof, PlonkVerificationKeyEvals (7 sigma+15 coeff+6, to_list ordonné testé)** ; restent : Plonk.In_circuit (scalaires dérivés — en pratique calculés par finalize), Spec/typ (encodage circuit hlist) |
| `plonk_types.ml::All_evals` | `src/all_evals.rs` | ✅ **factor testé** : `AllEvals` (ft_eval1 + public_input + evals aux 2 points) sur les types kimchi ProofEvaluations/PointEvaluations ; `factor` sépare les evals appariées par point == evals bruts de la preuve ; `actual_evaluation_circuit` (combinaison Horner des chunks) dans ft_eval_circuit.rs, testé |
| `per_proof_witness.ml`, `reduced_messages_for_next_proof_over_same_field.ml` | `src/recursive_step.rs`, `src/step_witness.rs`, `src/hash_messages.rs`, `src/composition_types.rs` | 🟨 premier per-proof witness step porté et validé : evals step flattenées, x_hat lagranges, statement width-1, messages_for_next_step hash, `RecursionChallenge`. Reste : types/API génériques pour N preuves et règles inductives, reduced-messages same-field complet, padding/dummy proofs dans le flux général |
| `verification_key.ml`, `side_loaded_verification_key.ml` | ⬜ | VKs (side-loaded = compat o1js) |
| `proof.ml`, `verify.ml` | ⬜ | preuves pickles + vérification out-of-circuit |
| `compile.ml`, `inductive_rule.ml`, `tag.ml`, `types_map.ml`, `requests.ml` | ⬜ | l'API utilisateur (ZkProgram-like) — en Rust : traits + génériques au lieu des GADTs |
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

### Ce qu'il manque maintenant

- **Récursion N>1 / règles inductives** : transformer le harness
  `prove_base_case + prove_recursive_step` en API générique capable de
  chaîner plusieurs steps/wraps et plusieurs branches. La première brique
  d'API est maintenant portée et le commitment de statement générique côté
  wrap est prêt ; la plomberie `PerUnfinalized` côté wrap est branchée. Il
  reste à prouver le wrap d'un step proof width>0 avec le témoin désormais
  préparé, puis le bouclage step→wrap répété.
- **Vrai wrap VK** : remplacer les points VK factices par le vrai VK obtenu
  après compilation du wrap circuit, ce qui implique une compilation en deux
  passes et les domaines Pickles paddés complets.
- **Padding Pickles complet** : intégrer les preuves non vérifiées, dummy
  commitments/evals/challenges et `reduced_messages_for_next_proof` dans le
  flux normal, pas seulement dans les helpers de test.
- **Parité Mina** : valider la sérialisation/RO/statement exacts contre Mina,
  pas seulement contre kimchi Rust et les mirrors locaux.
- **API utilisateur** : porter `compile.ml`, `inductive_rule.ml`, `tag.ml`,
  `types_map.ml` sous forme Rust idiomatique pour exposer un équivalent
  ZkProgram/prove/verify.
