# Port de Pickles (OCaml → Rust) — branche `pickle-rs`

Référence OCaml : `~/Projects/mina/src/lib/crypto/pickles` (49 modules).
Socle : le crate `snarky` (DSL + constraint system, parité de gates validée
contre l'OCaml) ; consommateur cible : o1js (branche `pickle-rust`,
voir `o1js/RUST_MIGRATION.md`).

Méthode éprouvée sur snarky : porter module par module, avec à chaque étape
un test de parité contre l'implémentation kimchi/OCaml existante.

## Principe d'audit — fidélité à l'OCaml

Ce code sera audité et doit correspondre le plus possible à la version de
base OCaml (`~/Projects/mina/.../pickles`). **Tout changement qui rapproche
le code de la structure OCaml et qui est NEUTRE (ni régression de tests, ni
changement de compteurs de gates) doit être committé quand même** — la
fidélité au source OCaml est une valeur en soi pour l'auditabilité, pas
seulement l'optimisation de la parité de gates. Ne pas rejeter un
refactor « fidèle mais gate-neutre » : le committer avec un message qui
dit qu'il aligne la structure sur l'OCaml sans effet gate. Vérifier
toujours l'absence de régression (recorded 9/9 : N0/N1/N2).

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

**Dernier écart Generic (508 vs 569, −61) — MÉCANISME DÉFINITIF.**
6/7 gate types exacts (Poseidon 1001, CompleteAdd 258, VarBaseMul 663,
EndoMulScalar 184, EndoMul 2464, public input 40=40, 8192 rows). L'écart
Generic n'est PAS un simple manque mais une **redistribution** (carte par
région de 500) :
- 0-500 : rust +31 (on sur-émet) ; 3500 : rust +41 ;
- 500-1500 : jsoo +109 (on sous-émet) ; 2000 : jsoo +24.

Localisation exacte du plus gros bloc manquant : **139 rows du motif
`o = x1 − x2` (`-1,1,-1,0,0`), en région 500-1500, ENTRE deux CompleteAdd**
(ex. rows jsoo 700-703 encadrées par CompleteAdd 699/704), avec une
constante `E` dans les demi-lignes voisines (`1,0,0,0,E`).

Cause : OCaml `reduce_to_v` (snarky `plonk_constraint_system.ml`)
**matérialise chaque constante passée à un gate en variable interne** via
`cached_constants` — un generic `x = E` (`[1,0,0,0,-E]`) par coordonnée
Lagrange constante fournie à un `add_fast`/CompleteAdd/scale dans le fold
`x_hat` et le `check_bulletproof`. Nous gardons ces coordonnées en
`FieldVar::Constant` repliées dans le gate → pas de generic. C'est ce qui
manque en 500-1500, et le décalage pousse les autres régions (d'où
sur-émission ailleurs et `type=2344` rows au mauvais type par cascade).

Pistes réfutées (toutes revertées, 9/9 préservé) : VK/h constantes
(pire), seal add_fast (no-op — les entrées étaient déjà des vars),
OptSponge à flags constants (no-op — se replie), reduce EcScale (no-op),
combine_commitments sg_old optionnel (casse EC), flush par label
(overshoot).

**Fix tenté (materialize en x_hat) = NO-OP** : x_hat n'a qu'UN terme (le
digest du step, public input step = 1 slot), donc matérialiser ses
constantes Lagrange/H n'ajoute que ~6 generics, pas 61 — et ses points
étaient déjà des vars. Reverté, step toujours FULL MATCH. Les 139 rows
`o=x1−x2` sont donc dans les opérations EC MULTI-POINTS de la boucle IVP :
`bulletproof.rs::{combine_commitments, check_bulletproof_equation,
bullet_reduce_terms}` et `commitments.rs::ft_comm`, qui manipulent 28+
points (VK comms, sg_old, w/z/t, lr) via add_fast/EndoMul/scale.

**Wrap parity — Generic 556/569, 13 net.** Autres gate types EXACTS,
step FULL MATCH, recorded 9/9 (N0/N1/N2).

Confirmations de FIDÉLITÉ OCaml (vérifiées, aucun changement requis) :
- `snarky::cvar::equal_constraints` = OCaml `Utils.equal_constraints`
  (`z_inv·z = 1-r` puis `r·z = 0`, ordre identique) ✓.

Gains committés : lookups_per_row_3/4 (`bd6f1b8d2a`, +5 Generic), fix N2
(`6c2a153c95`, 9/9), forbidden-check remonté avant which_branch
(`969e09edea`, marginal +6 rows).

**Reste — offset de pairing à l'ouverture du circuit wrap.** Séquence de
contraintes HL du wrap jsoo (via instrumentation OCaml) : **2 R1CS puis
~28 Equal** (kind `Equal` = `assert_equals`/seals directs, PAS notre
gadget equal qui émet du R1CS). Notre ouverture diffère → offset qui
cascade (type=1989). À investiguer :
- QUELS sont les 2 R1CS + 28 Equal d'ouverture d'OCaml `wrap_main` (avant
  le corps) — probablement le one-hot `which_branch` (booleanité R1CS) +
  des seals de valeurs différées du statement (split/pack). Notre ordre
  (forbidden R1CS puis which_branch) ne correspond pas.
- count `forbidden_shifted_values_fq` = **2** : suspect (les 28 Equal jsoo
  suggèrent plus de valeurs/asserts au début). Vérifier vs OCaml.
Méthode : capturer les 2 logs HL (jsoo : `rust-pickles-vk-parity.ts` avec
jsoo instrumenté à `89edaa3204` ; rust : `SNARKY_LOG_HL_CONSTRAINTS`),
extraire la sous-séquence wrap ordonnée de chaque, aligner → 1ère
divergence = la contrainte exacte à corriger.


⚠️ **TOUJOURS tester les 3 tailles de preuve à chaque changement du
pipeline pickles** (`cargo test -p pickles --release --test recorded`) :
- **N0** (`recorded_square`, `recorded_ec_add`) : cas de base, 0
  accumulateur ;
- **N1** (`recorded_n1_cycle`, `recorded_chained_n1`,
  `recorded_stable_n1_chain`) : 1 preuve récursive, step 2^14 ;
- **N2** (`recorded_n2_cycle`) : 2 preuves vérifiées, step width-2 2^16,
  wrap 2^15 — c'est le cas qui expose les hypothèses de domaine/SRS/
  branch-data cachées (N0/N1 les masquent car leurs domaines coïncident).
Ne PAS conclure « 9/9 » en ne lançant que N0/N1 : plusieurs régressions
(codex + moi) ne se voyaient que sur N2. Idem `--test recursion` et
`--lib` pour la couverture complète.


**Fausses pistes testées aujourd'hui (ne PAS refaire)** :
- witness des slots zeta Type2 seul → aucun effet gate ;
- assertion séparée de messages_for_next_step_proof → aucun effet gate ;
- remplacer le masque physique sg_old par le masque calculé → casse le
  witness ;
- (antérieures) VK/h constantes → pire ; seal add_fast → no-op ;
  OptSponge flags constants → no-op ; materialize x_hat → no-op.

Dumps : `/tmp/claude-1000/{wrap-circuit-*.json, jsoo-constraints.log}`.
