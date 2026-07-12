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

## Handoff WRAP — parité gates (état courant)

**Generic 556/569 (13 net), tous les autres gate types EXACTS, step FULL
MATCH, recorded 9/9 (N0/N1/N2).** Toujours tester N0/N1/N2 après tout
changement wrap (`cargo test -p pickles --release --test recorded`), puis
mesurer avec `o1js/src/tests/rust-pickles-wrap-gates-diff.ts` (nécessite de
reconstruire le napi : `cd o1js && PROOF_SYSTEMS_ROOT=~/Projects/proof-systems
PATH=$PWD/node_modules/.bin:$PATH bash scripts/build/native/build.sh`).

Acquis récents :
- **forbidden `Other_field.check` en ordre INVERSE** (commit `8aa1d16c4e`) :
  OCaml applique le check aux slots fq `[cip;b;zsl;zds;perm]` de l'arrière
  vers l'avant (perm→row40 … cip→row66). Boucle `stmt[0..5].iter().rev()`.
  → rows 0-4 iso, divergence 3207→3203. Première divergence désormais row 5.
- Confirmations de fidélité (code déjà conforme) : `cvar::equal_constraints`
  = OCaml `Utils.equal_constraints` ; `which_branch` (`equal(0)`+assert) =
  `One_hot_vector.of_index` length 1.

**Direction du gap : rust MANQUE des generics (jsoo 569 > rust 556).**
TOUT retrait empire la divergence ET éloigne le compte. Il faut AJOUTER les
bons generics au bon endroit, pas retirer.

**OUTIL CLÉ — labels des DEUX côtés via `SNARKY_LOG_CONSTRAINTS=1`.**
`SNARKY_LOG_CONSTRAINTS=1 ./run src/tests/rust-pickles-wrap-gates-diff.ts
> log.txt` émet :
- côté RUST : `<row>: gen1:[api.rs:LIGNE] - [label]` (le build jsoo bundle
  aussi notre napi). 2 builds wrap ; le DERNIER (2e `^0:` avec
  `api.rs:416 equals_1`) est le dump. **`dump_row = log_row + 40`**.
- côté JSOO/OCaml : `CONSTRAINT <Type>(... @ File "…/wrap_main.ml", line N
  | <labels>)` — le flux de contraintes OCaml AVEC fichiers/lignes ! C'est
  la référence directe. Séquence d'ouverture du wrap OCaml sauvegardée dans
  `pickles/ocaml-wrap-constraint-sequence.txt` (run-length, ligne innermost).

**Séquence d'ouverture OCaml (wrap_main.ml) désormais connue :**
`2×R1CS:155` (which_branch One_hot_vector.of_index) → `1×R1CS:170`
(actual_proofs_verified_mask = `Pseudo.choose(step_widths)`) → `1×Equal:181`
(domain_log2 `Pseudo.choose` + branch_data assert) → `56×Equal:204`
(**`choose_key`** : sélection des 28 points VK depuis les clés CONSTANTES,
= `sum which_branch_i · key_i`, 56 coords sealed) → on-curve (Square/R1CS
répétés sur les 28 points sélectionnés).

**Différences rust identifiées (à corriger, direction = AJOUTER/aligner) :**
1. `domain_log2` : rust utilise `w.step_domain_log2` CONSTANT (api.rs:441) ;
   OCaml le calcule via `Pseudo.choose` (émet contrainte). Rust manque cette
   contrainte.
2. **VK : rust fait `mkpt` (witness+on-curve) puis `assert_vk_point`
   (56 Equal) ; OCaml fait `choose_key` (56 Equal de SÉLECTION depuis
   constantes) PUIS on-curve sur les points sélectionnés.** Structure et
   ordre différents → c'est probablement la source principale du delta de
   coeffs 73-178 ET du gap de 13. Réécrire le bloc VK en `choose_key` :
   pour chaque coord, `point_coord = which_branch0 · const` (scale booléen),
   sealed, puis on-curve — au lieu de witness+assert.
3. `prev_proof_state exists` (wrap_main.ml:191, entre branch_data et
   choose_key) : exists 2 unfinalized dummy (Type2 + assert_16_bits). Rust
   le saute en base (`unfinalized: vec![]`).

**Ordre OCaml complet du wrap (via le flux jsoo, à suivre exactement) :**
which_branch(2 R1CS) → proofs_verified_mask Pseudo.choose(R1CS:170) →
domain_log2/branch_data(Equal:181) → **choose_key VK (56 Equal:204)** →
VK on-curve (28 pts Square/R1CS:155) → qq R1CS/Equal:155 → **messages/
openings on-curve (bloc Square/R1CS:471)** → **1er Poseidon à
wrap_main.ml:503** (sponge_inputs.ml). 
⚠️ SUBTILITÉ ARCHITECTURE : le 1er Poseidon OCaml est à :503, APRÈS les
on-curve messages/openings (:471) — PAS un sponge d'index précoce. Notre
`vk_digest` (Poseidon rust row 179) ne mappe donc pas 1:1 sur un Poseidon
OCaml à cette position ; OCaml calcule le digest d'index autrement (absorbé
dans un sponge existant, pas un `PoseidonSponge::new()` séparé). Le gain de
`6abbec7b88` (remonter le sponge) reste net (2917) mais l'alignement exact
du sponge demande de réconcilier l'architecture digest OCaml (étudier
wrap_main.ml:503 + `incrementally_verify_proof`). C'est probablement là que
se cachent les 13 Generic + le gros du type=1926.

**Changement fidèle committé (gate-neutre)** : `618542d6a2` réécrit la
sélection VK en `choose_key` (branch0.scale+seal) comme OCaml. Divergence
inchangée (2917) mais structure alignée — principe d'audit.

**Fausses pistes (vérifiées empiriquement, NE PAS refaire) :**
- VK points en constantes (`cpt` au lieu de `mkpt`) : 556→**500**, div
  3203→3402. jsoo A les on-curve checks VK. Garder `mkpt`.
- `sg_olds` witnessé AVANT le sponge : div 2917→**3203**. Pas les
  `prev_step_accs`.
- Witnesser 2 points dummy on-curve (valeurs sg_olds) avant le sponge :
  556→560 mais div 2917→**3225**. Les dummies naïfs ne matchent pas.
- Retirer `assert_vk_point` (croyant qu'OCaml contraint la VK via le seul
  digest) : 556→**528**, div 2917→**3387**. jsoo contraint bien la VK
  par-point. Garder les asserts.

**Interleaving pré-Poseidon — FAIT en partie** (commit `6abbec7b88`) : le
sponge `vk_digest` (`absorb verifier index`) est désormais émis juste après
la sélection de la VK, avant les points de payload. Divergence 3203→**2917**
(type 1926, coeffs 561), Generic inchangé 556. Premier Poseidon : rust **179**
vs jsoo **231** (était 312) — on est passé de trop tard à un peu trop tôt.

**Reste — les 52 Generic entre VK et sponge (base case padding).** jsoo a 52
Generic de plus que rust avant le 1er Poseidon. En lisant `wrap_main.ml`
(≈301-360), OCaml, APRÈS `assert_consistent` (feature flags) et AVANT le
sponge d'index, exists :
- `prev_step_accs` : `Vector.wrap_typ Inner_curve.typ Max_proofs_verified.n`
  = **2 points paddés dummy, checkés on-curve** (même en N0) ;
- `old_bp_chals` : vecteurs de challenges ;
- `new_bulletproof_challenges` : `evals` + `wrap_domain_indices`.
Rust en base case a `unfinalized: vec![]` → il SAUTE ces exists (les
`prev_step_acc`/`old_bulletproof_challenges` vivent dans `PerUnfinalized`,
vide en N0). C'est le même gap « dummy unfinalized padding » que côté
28-Equal : OCaml pad toujours à `Max_proofs_verified=2`. Prochain pas :
witnesser 2 `prev_step_accs` dummy (on-curve) + `old_bp_chals` + `evals`
AVANT le sponge d'index, sans lancer de finalize (should_finalize=false),
en surveillant que EndoMul/Poseidon/EndoMulScalar (compteurs EXACTS) ne
bougent pas — seuls des Generic doivent s'ajouter.

## Handoff historique — parité VK o1js

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

Confirmations de FIDÉLITÉ OCaml (vérifiées, code déjà conforme) :
- `cvar::equal_constraints` = OCaml `Utils.equal_constraints`
  (`z_inv·z=1-r` puis `r·z=0`) ✓ ;
- notre `which_branch` (`equal(0)` + assert==1) = OCaml
  `One_hot_vector.of_index` length 1 (`Field.equal 0 i` + `Assert.any`) ✓.

**GAP STRUCTUREL identifié — le vrai reste.** Séquence d'ouverture du wrap
jsoo (via instrumentation OCaml) : `which_branch` one-hot (2 R1CS) →
`branch_data` assert → **`exists prev_proof_state`** = OCaml witnesse
**2 unfinalized proofs DUMMY** (padding à max_proofs_verified=2, MÊME pour
N0) et `split_field` leurs valeurs différées Type2 (`Field.Assert.equal
(2y+is_odd) x` = 1 Equal chacune) → les **~28 Equal** d'ouverture.
Notre base wrap : `unfinalized: vec![]` = 0 (api.rs:1458) → on saute ce
bloc. Ajouter les 28 Equal (split de 2 dummies) au bon endroit fermerait
les 13 net ET la cascade type=1989.

**ATTENTION avant d'implémenter** : OCaml met should_finalize=false pour
les dummies → le `finalize_other_proof` tourne quand même mais son
résultat n'est pas asserté. Il faut ajouter UNIQUEMENT l'`exists`/split
(28 Equal), PAS un finalize qui émettrait des EndoMul/Poseidon et
casserait les compteurs EXACTS (EndoMul 2464, Poseidon 1001). Vérifier
après ajout que ces compteurs ne bougent pas et que N0/N1/N2 passent.
Piste : peupler `w.unfinalized` de 2 dummies dont le witness ne déclenche
que le split_field, ou ajouter un bloc `exists_dummy_unfinalized` distinct
avant le traitement des vrais unfinalized.


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

## Correction du handoff — 2026-07-12

La piste « `prev_proof_state` dummy manquant » ci-dessus est **réfutée pour
le programme o1js minimal de référence**. Une vérification directe avec
`o1js/src/tests/rust-pickles-step-gates-diff.ts` donne :

- `public_input_size: jsoo=1 rust=1` ;
- 512 rows et histogrammes identiques ;
- `STEP GATES: FULL MATCH`.

Le step de base n’expose donc pas un statement public étendu contenant deux
unfinalized proofs. Ajouter des `split_field` synthétiques dans le wrap est
incorrect : 13 splits ferment artificiellement le compteur Generic
(`569=569`), mais font monter les divergences structurelles à 3778 rows.
Cette tentative a été revertée et ne doit pas être reprise.

L’état source vérifié avant cette tentative est : wrap à 8192 rows des deux
côtés, tous les types de gate non-Generic exacts, `Generic 556 vs 569`.
Le travail restant concerne l’ordre et la réduction des contraintes privées
du wrap — en premier `Other_field.check`, puis les chemins qui réutilisent
les challenges `beta`/`gamma` — et non le layout public du step.
