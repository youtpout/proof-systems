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

**INSTRUMENTATION OCAML FAITE — diff par gadget obtenu.**

Côté Rust : `SNARKY_LOG_CONSTRAINTS=1 cargo test -p pickles --release
--test recorded recorded_square -- --nocapture` → `row: loc - labels`.

Côté OCaml (nouveau) : logger ajouté dans
`o1js/src/mina/src/lib/snarky/src/base/checked_runner.ml::add_constraint`
(gaté par `SNARKY_LOG_CONSTRAINTS`, imprime `CONSTRAINT <kind> @ <label
stack>` via la pile `with_label`). Capture :
`SNARKY_LOG_CONSTRAINTS=1 ./run src/tests/rust-pickles-vk-parity.ts
2>/dev/null | grep '^CONSTRAINT '`.
GOTCHA build : le proof-systems IMBRIQUÉ (`src/mina/.../proof-systems`)
avait divergé (commits "Mina reduced messages" → bindings incompatibles
avec pickles.ml, erreurs `Fp.t array`). Ramené à la base mina-compatible
`89edaa3204` pour builder jsoo (garder checked_runner.ml). Vendor cargo
régénéré (`cargo vendor` + vider les maps `files` des `.cargo-checksum.json`
+ retirer `.github`/symlinks cassés). Note : la base 89edaa n'a pas
`fq_prover_to_json` → pour re-differ le wrap, remettre le nested à
`866c3ab277` (bundled wasm) OU cherry-pick fq_prover sur 89edaa.

**DIFF DÉFINITIF (kinds de contraintes, wrap+step) :**
| kind | jsoo | rust (approx) |
|------|------|------|
| Equal | **584** | ~124 (`assert equals`+`equals_1/2`) |
| R1CS | 349 | ~123 (`checked_mul`) |
| Square | 265 | ~264 (on-curve+…) ✓ |
| EC_add_complete | 264 | 265 ✓ |
| EC_endoscale | 79 | ✓ | EC_scale 15, EC_endoscalar 25 |

**CAUSE : jsoo émet 584 `Equal` vs ~124** — 460 de plus. Répartition des
Equal jsoo par gadget : `endo` 158, `wrap_verifier:580` (check_bulletproof)
133, `hash_messages_for_next_step_proof` 110, `wrap_main:204` 56,
`absorb verifier index` 54. Ce sont des **seals/asserts d'intermédiaires**
(`Util.Wrap.seal`, `Field.Assert.equal`) qu'OCaml fait systématiquement
avant de réutiliser une valeur, et que nous omettons (on garde les
`compute` non scellés). Une fraction (~61 net, ~139 en région 500-1500)
devient des rows generic `o=x1−x2` (`-1,1,-1,0,0`) qu'on n'a pas.

**FIX** : ajouter les seals qu'OCaml fait dans les gadgets à fort écart
d'Equal — en priorité `scalar_challenge.rs::endo` (jsoo 158 Equal : sceller
les intermédiaires xq/yq/s/xr/yr par round ? à vérifier vs EndoMul déjà
exact), `bulletproof.rs` (check_bulletproof 133), `hash_messages.rs` (110).
Attention : ne pas bouger EC_add_complete/EndoMul (déjà exacts) ; vérifier
le step reste FULL MATCH après chaque ajout. Le diff par gadget (ci-dessus)
dit exactement où chercher — plus de devinette.

État committé avant reprise Codex : Generic 508 vs 569, 6/7 gate types
exacts, 9/9 recorded, step FULL MATCH. Instrumentation OCaml sur disque
(mina/snarky, sous-module).

**Reprise Codex — deux contraintes wrap top-level portées** :
- `af073a69ea` (`Port wrap branch data assertion`) : assertion
  `branch_data = domain_log2 * 4 + proofs_verified` dans `WrapCircuit`,
  portée aussi dans la préparation récursive. Effet mesuré : Generic
  **508 → 509**, step toujours FULL MATCH.
- `a3e38bcfca` (`Constrain selected wrap verification key`) : port du bloc
  `wrap_main.ml:204` / `choose_key` en contraignant les 28 engagements de la
  VK step witnessée à la clé sélectionnée. Effet mesuré : Generic
  **509 → 537**, step toujours FULL MATCH.

État actuel mesuré avec `rust-pickles-wrap-gates-diff.ts` :
- public input **40 = 40**, rows **8192 = 8192** ;
- Poseidon **1001 = 1001**, CompleteAdd **258 = 258**,
  VarBaseMul **663 = 663**, EndoMulScalar **184 = 184**,
  EndoMul **2464 = 2464** ;
- reste uniquement le compteur **Generic 537 vs 569** (écart net **−32**)
  et donc **Zero 3085 vs 3053**.

Note importante : un essai de seal global de `DuplexState::absorb`
(`state[i] <- seal(state[i] + x)`, comme `sponge_inputs.ml`) augmente bien
les `Equal` HL, mais **ne change pas le histogramme Kimchi wrap**. Même chose
pour une matérialisation explicite des constantes `CompleteAdd` via
`assert_equals`. Le reliquat de 32 rows doit donc être fermé par les vraies
contraintes `R1CS`/`Field.Checked.mul` encore absentes, principalement autour
de `check_bulletproof` / `Other_field.Packed`, pas par des seals aveugles.

**Instrumentation Rust HL AUSSI faite** (`SNARKY_LOG_HL_CONSTRAINTS=1`,
`snarky/src/runner.rs::add_constraint`) : log constraint-level (avant
expansion en gates), même granularité que le log OCaml → **séquences
comparables 1:1**. Capture :
`SNARKY_LOG_HL_CONSTRAINTS=1 cargo test -p pickles --release --test
recorded recorded_square -- --nocapture 2>/dev/null | grep '^HLCONSTRAINT'`.

**Diff kind-level DÉFINITIF** (rust recorded_square = two-pass, ÷2 ; jsoo
vk-parity = 1 pass ; step à 0 diff donc tout l'écart est wrap) :
| kind | jsoo | rust÷2 | écart |
|------|------|--------|-------|
| Equal | 584 | 302 | **jsoo +282** |
| R1CS | 349 | 243 | **jsoo +106** |
| Square | 265 | 323 | rust +58 (on-curve 88 vs 73) |
| EC_add_complete | 264 | 265 | ✓ |
| EC_endoscale/scalar/scale | 79/25/15 | ✓ | |

OCaml émet **+282 Equal (seals `Util.Wrap.seal`/`Field.Assert.equal`) et
+106 R1CS (checked-muls)** d'intermédiaires que nous calculons sans
sceller. Répartition Equal jsoo : endo 158, check_bulletproof 133,
hash_messages 110, wrap_main:204 56, absorb 54.

**MÉTHODE pour fermer (traçable, plus de devinette)** :
1. Capturer les deux logs HL (OCaml : `rust-pickles-vk-parity.ts` ;
   Rust : `recorded_square`).
2. Extraire la sous-séquence WRAP de chaque (labels wrap_main/
   wrap_verifier/bulletproof/combine côté jsoo ; circuit final côté rust),
   en ORDRE.
3. Aligner les séquences de kinds → première divergence = première
   contrainte OCaml qu'on n'émet pas → identifie le gadget + la ligne
   exacte à corriger (ajouter le seal/mul).
4. Ajouter le seal, re-tester (cargo test recorded), re-diff, itérer.
   Vérifier à CHAQUE fois : step reste FULL MATCH, EC/EndoMul inchangés.

Fichiers : logs `/tmp/claude-1000/{jsoo-constraints.log, rust-hl.log}`.
Nested proof-systems : jsoo needs `89edaa3204`, bundled wasm needs
`866c3ab277` (fq_prover) — actuellement à 866c3ab277.
Dumps : `/tmp/claude-1000/{wrap-circuit-*.json, jsoo-constraints.log}`.
