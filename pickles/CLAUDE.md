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

### Essais récents rejetés (ne pas réintroduire)

- **Supprimer `actual_proofs_verified_mask`** dans `wrap_main.rs` : ce masque
  paraît mort côté Rust, mais son retrait donne `Generic 550/569` et **2920**
  lignes divergentes, contre 2869 pour l'état `ce01aa6d9f`. Il émet donc une
  partie des contraintes attendues ; ne pas le supprimer.
- **Utiliser ce masque dynamique dans `verify`** : l'OCaml le transmet bien au
  vérificateur, mais le port Rust ne représente pas encore les accumulateurs
  optionnels de la même façon. Les preuves recorded échouent alors sur
  `wrap_main: verify step proof` (`equal_g = 0`). Masquer le transcript seul,
  ou transcript + combinaison, est insuffisant : il faut porter le type
  `Opt`/la combinaison OCaml d'un bloc.
- **Dériver `first_zero` de `proofs_verified`** à la place du témoin : pour
  N0, `branch0 * 0` se simplifie en constante et retire 6 Generic
  (`550/569`). Rejeté tant que `Pseudo.choose` n'est pas reproduit sans cette
  simplification.
- **Différer les checks on-curve des openings** : la première divergence de
  type est bien après les deux Generic 594--595, mais déplacer ces checks sans
  porter tout le scheduling du vérificateur ne peut pas être validé ; essai
  reverté avant commit.

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

**Différences rust identifiées :**
1. ~~`domain_log2` constant~~ : FAUX, rust fait déjà `branch0·const`
   (api.rs:440) et `proofs_verified = branch0·len` (api.rs:430). L'ouverture
   (which_branch/proofs/domain/branch_data) matche OCaml. Rien à faire.
2. **VK `choose_key`** : FAIT (`618542d6a2`), gate-neutre.
3. `prev_proof_state exists` (wrap_main.ml:191) : exists 2 unfinalized
   dummy (Type2 + assert_16_bits). Rust le saute en base.
4. **BLOCAGE PRINCIPAL — POSITION du digest d'index (Poseidon).**
   CORRECTION : l'architecture MATCHE. OCaml calcule bien un `index_digest`
   via un sponge SÉPARÉ (`Sponge.create` puis squeeze,
   wrap_verifier.ml:850-866, label "absorb verifier index"), exactement
   comme notre `vk_digest` (api.rs). La différence est UNIQUEMENT la
   POSITION : OCaml le calcule DANS `incrementally_verify_proof` à IVC
   Step 2 (wrap_verifier.ml:877 `absorb sponge Field index_digest`), donc
   APRÈS que `messages`/`openings_proof` soient déjà témoins (leurs exists
   sont AVANT l'appel verify, wrap_main.ml:440-476), et juste avant
   `absorb sg_old`. Rust calcule `vk_digest` dans api.rs et le passe en
   paramètre à `verify`.
   ⚠️ EMPIRIQUE DÉROUTANT : l'optimum de gate-parity (2917, `6abbec7b88`,
   sponge AVANT messages) NE coïncide PAS avec la position OCaml (après
   messages/openings, au début du corps de verify). Reculer vers la
   position OCaml donne 3203 (pire). Cela indique que le reste n'est pas un
   seul déplacement propre mais une COMBINAISON : position du digest +
   `prev_proof_state` dummy exists (piste 3) + pairing double-generic. 
   ⚠️ `verify` (step_verifier.rs:50) est PARTAGÉ avec le step (FULL MATCH) :
   le modifier pour calculer le digest en interne risque de casser la
   parité step. Il faut isoler le chemin wrap. Prochaine passe : calculer
   `vk_digest` au DÉBUT du corps de `verify` (depuis `vk`, déjà passé),
   uniquement pour le wrap, à la position IVC Step 2 — en gardant le step
   intact — puis re-mesurer, et traiter la piste 3 en parallèle.

**⚠️ DÉCISIF — openmina n'est PAS le template du base case o1js.**
Vérifié empiriquement : le flux de contraintes o1js du wrap (via
`SNARKY_LOG_CONSTRAINTS`) contient **ZÉRO** occurrence de `finalize` /
`unfinalized` / `finalize_other_proof`. Le base-case wrap o1js n'a **aucun
unfinalized proof** à finaliser → notre `unfinalized: vec![]` est CORRECT.
En revanche openmina (mina) pad TOUJOURS à `Max_proofs_verified=2` et
finalise 2 dummies (`wrap.rs:2880 finalize_other_proof`). Les deux circuits
DIFFÈRENT sur le base case. C'est pourquoi tous les reorders guidés par
openmina régressent (3844/3203) : ils poussent vers la structure mina.
→ **NE PAS réécrire le corps wrap en miroir openmina.** openmina reste utile
pour l'ordre CENTRAL partagé (sponge/IPA dans `incrementally_verify_proof`,
`choose_key`) mais PAS pour le squelette base-case. La référence pour le
base case o1js = le flux jsoo `SNARKY_LOG_CONSTRAINTS` (fichiers émetteurs :
wrap_verifier.ml 1249, wrap_main.ml 950 [lignes 155/204/471/480/503],
scalar_challenge.ml 420, sponge_inputs.ml 298). Le reste (2917) est un
alignement FIN d'ordre dans la région verify (scalar_challenge/sponge/IPA),
pas un changement structurel — à traiter contre le log jsoo o1js.

**RÉFÉRENCE RUST (partielle) : openmina (`~/Projects/mina-rust`).**
`crates/ledger/src/proofs/{wrap,step,verification,unfinalized,opt_sponge}.rs`
est un port Pickles Rust COMPLET et fonctionnel (interop réseau Mina) → son
ordre d'opérations EST celui d'OCaml. `wrap_main` (wrap.rs:2791) donne
l'ordre exact : which_branch → masks/domain → `exists_prev_statement`
(witnesse les unfinalized, sans check) → `choose_key` VK →
`prev_step_accs`(=sg_olds) → `old_bp_chals` → `evals`+**`finalize_other_proof`
par unfinalized** → hash prev → `openings_proof` → `messages` →
`incrementally_verify_proof` (qui calcule le `index_digest` en INTERNE via un
sponge séparé, wrap.rs:2289, puis absorb digest → sg_old → x_hat).

⚠️ LEÇON (testé cette session) : les moves PARTIELS vers l'ordre openmina
RÉGRESSENT tous depuis le 2917 (optimum LOCAL de la structure actuelle) :
- digest calculé dans `incrementally_verify_proof` (position openmina) au
  lieu d'api.rs → **3844** (pire) ;
- `vk_digest` déplacé après messages en api.rs → **3203** ;
- sg_olds/openings/messages réordonnés seuls → **3203**.
→ Atteindre < 2917 exige une RÉÉCRITURE COMPLÈTE du corps wrap (api.rs +
wrap_main.rs) en miroir ligne-à-ligne d'openmina `wrap_main`, PAS des moves
incrémentaux. Utiliser openmina comme template, réécrire d'un bloc, puis
vérifier recorded 9/9 + wrap-diff. Attention au modèle : openmina =
witness-gen (les `exists` n'émettent pas de contraintes), nous = snarky
(tout émet) → mapper l'ordre des opérations qui ÉMETTENT des contraintes
(checks on-curve, range, R1CS, sponge), pas les exists nus.

**OUTIL DE LABELS ALIGNÉS (committé `3409b070ed`) — utilisable.**
Le dump JSON rust porte maintenant `labels[]` alignés 1:1 aux gates
(`WrapCircuitDump.labels`, via `snarky GateSpec.label` → finalize →
`ProverIndexWrapper::gate_labels()`). Instrumentation pure, gates inchangés.
Charger `wrap-circuit-rust.json`, `d['labels'][row]` donne l'op émettrice
(ex `gen1:[on-curve check] gen2:[checked_mul]`, `Poseidon`, `equals_1`,
`feature flag bit`, `assert equals`). Le pattern coeff `05` (=b de y²=x³+5)
= on-curve check.

**DIAGNOSTIC via labels — première divergence de TYPE à row 179 :**
- ordre RUST : forbidden(40-74) → flags(75-92) → choose_key/branch(93-121)
  → VK on-curve(122-178) → **vk_digest sponge Poseidon(179-541)** →
  messages+openings on-curve(542+).
- ordre JSOO : … → VK on-curve(103-166) → **messages on-curve(181-230)** →
  sponge(231+) → openings/lr on-curve (plus tard).
- Donc jsoo witnesse les MESSAGES on-curve AVANT le sponge (openings APRÈS),
  rust met TOUT (messages+openings) après le sponge.

**Test fait (régresse, mais instructif) :** déplacer les messages AVANT le
vk_digest sponge (openings restent après) → 1er Poseidon 179→**225** (jsoo
231, quasi aligné !), type 1989→1951, MAIS coeffs 757→**804**, net **3203**
(>2917). Les coeffs des messages on-curve à 179-224 diffèrent de jsoo
181-230 → l'ORDRE/valeurs internes des points messages (w_comm 15 / z_comm 1
/ t_comm 7) ou la structure mkpt ne matchent pas la typ messages jsoo.
**Test affiné (messages + sg_olds avant sponge, openings après)** :
1er Poseidon 179→**229** (jsoo 231, à 2 rows près !), type 1989→**1943**
(mieux), MAIS coeffs 757→**808** (pire) → net **3203** (>2917). Donc :
- La STRUCTURE est correcte : witnesser messages + sg_olds on-curve avant le
  sponge aligne quasi-parfaitement le bloc Poseidon (position + type↓).
- Le blocage résiduel est les COEFFS : le pairing double-generic à la
  frontière des on-curve messages/sg_olds diffère de jsoo (les on-curve ont
  pourtant les mêmes coeffs `05` — donc c'est le PAIRING des demi-generics
  aux jonctions, ou une réduction en trop, qui décale les coeffs en aval).
- 2917 garde de meilleurs coeffs mais un type/position faux (sponge trop tôt).
Aucun des deux n'est pleinement correct : il faut messages+sg_olds-avant
(pour type/Poseidon) ET aligner le pairing double-generic aux jonctions
on-curve (pour coeffs). Le pairing est piloté par l'ORDRE exact d'émission
des demi-generics (equal_constraints, seal, on-curve Square/mul) à ces rows.
**Prochain pas** : garder messages+sg_olds-avant (structure juste), puis avec
le tool comparer coeff-à-coeff rust vs jsoo autour de 229-260 et 340+ pour
trouver le demi-generic mal apparié (souvent 1 reduction/seal en trop ou en
ordre inverse), le corriger dans incrementally_verify.rs / oracles.rs.

**LOCALISATION PRÉCISE du reste (comptage Generic par fenêtre) :**
- rows **0-231 : MATCH EXACT** (231 Generic des deux côtés) → tout
  l'opening (forbidden, which_branch, choose_key, VK on-curve, feature
  flags, 1er sponge) est aligné.
- rows 231-543 : rust **+79** Generic (jsoo 24, rust 103).
- rows 543-1024 : rust **−74** (jsoo 108, rust 34).
- rows 1024-2048 : rust −34 ; 2048-4096 : rust +29 ; 4096-8192 : rust −14.
- Net −14 ≈ le déficit de 13. Les +79/−74 se compensent en grande partie
  → c'est un **décalage de PHASE** dans le corps du verify, pas des
  contraintes manquantes : rust fait le travail Generic (x_hat / packing du
  statement / décompositions de scalaires) PLUS TÔT que jsoo, qui fait
  d'abord des absorbs Poseidon.
- Mon ordre HAUT-NIVEAU de `incrementally_verify_proof` (incrementally_verify.rs)
  matche déjà OCaml (absorb index_digest → sg_old → x_hat →
  w_comm → squeeze beta/gamma → z_comm → alpha → t_comm → zeta). Donc la
  divergence est un SOUS-ordre fin dans `x_hat` (`public_input_commitment`
  / `statement_terms`, public_input.rs) et la phase IPA vs son scheduling.
  Prochaine passe : comparer finement `public_input_commitment` +
  `statement_terms` (rust) contre le bloc x_hat d'OCaml
  (wrap_verifier.ml:879-950 : partition constant/non-constant,
  `Add_with_correction`/`Cond_add`, `add_fast`, ordre des `lagrange`) —
  c'est là que rust émet 79 Generic trop tôt.

**Outillage testé et ses LIMITES (ne pas refaire naïvement) :**
- Comparaison HL : `SNARKY_LOG_CONSTRAINTS=1 SNARKY_LOG_HL_CONSTRAINTS=1`
  émet côté jsoo `CONSTRAINT <kind> @ file:line` (niveau add_constraint
  OCaml) et côté rust `HLCONSTRAINT <kind> @ label` (runner.rs add_constraint).
  MÊME vocabulaire de kinds (R1CS/Equal/Square/Poseidon/EC_add_complete/
  EC_endoscale/EC_endoscalar/EC_scale/Basic/Boolean) MAIS 3 mismatches
  bloquants pour un diff kind-pour-kind :
  1. GRANULARITÉ : jsoo logue `Equal`(1) pour un `Field.Checked.equal` là où
     rust logue `R1CS`+`R1CS`(2) via equal_constraints ;
  2. SÉPARATION wrap/step : le forbidden est labellisé `impls.ml` (présent
     aussi côté step/préambule dummy), wrap_main/wrap_verifier ne suffit pas
     à isoler proprement ;
  3. ÉMISSION vs DUMP : le dump réordonne (double-generic pairing), donc
     l'ordre HL d'émission ≠ l'ordre des rows du dump.
  → Un diff utile exige de NORMALISER la granularité (fusionner les paires
     R1CS de equal_constraints en un `Equal` logique) ET de segmenter
     wrap/step par bornes explicites. Non fait.
- Comptes HL wrap bruts : jsoo ~1154 (filtre wrap_main+wrap_verifier seul,
  sans forbidden), rust ~1178. Non concluant à cause des mismatches ci-dessus.

**Nature du reste (2917) : réorganisation structurelle, pas des fixes
locaux.** La région match rows 231-542, puis à row 543 : jsoo fait un bloc
Poseidon (permutation de sponge = absorb d'un champ), rust fait des Generic
de décomposition scalaire (coeffs avec `05` = endo). Symptôme général :
rust et OCaml atteignent des compteurs de gates IDENTIQUES (EndoMul 2464,
EndoMulScalar 184, Poseidon 1001 — tous exacts) mais via des ORDRES de
contraintes différents dans la région verify/sponge/scalar. Ex : le
`prev_proof_state` dummy exists + les assert_16_bits sur challenges dummy
d'OCaml sont émis AILLEURS chez nous et atteignent les mêmes totaux.
→ Conséquence : atteindre l'iso au niveau row demande un REFACTOR qui
reproduit la séquence exacte d'OCaml dans le corps de verify (absorb-order
du Fr-sponge, décomposition des scalar challenges, position du digest),
pas des retouches locales. 7+ expériences ciblées ont échoué ou été neutres.
C'est une passe dédiée, à faire en miroir strict de `wrap_verifier.ml`
`incrementally_verify_proof` + `finalize`, avec re-mesure à chaque
sous-étape, et en isolant le chemin wrap du step (verify partagé).

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

## Correction du handoff — 2026-07-12 (suite, codex)

**Le commit `ce01aa6d9f` ("Align wrap transcript witness order") AMÉLIORE
effectivement l'état, contrairement à ce que documentaient les essais
précédents (91bf44b457/acb2de2a2e) qui donnaient 3203.** Différence clé :
cet essai-ci ne se contente pas de déplacer `messages`/`sg_olds` avant le
sponge — il **recalcule `vk_digest` EN CIRCUIT depuis les 28 points de la
VK** (absorb direct des coordonnées `vk.sigma_init/…/endomul_scalar` dans un
`PoseidonSponge::new()`, api.rs:629-651) **au lieu de le witnesser**. C'est
cette combinaison (constants → variables déjà en main + réordonnancement)
qui débloque, pas le réordonnancement seul. Mesuré après rebuild napi :

- **divergence 2869** (record, contre 2917 précédent), Generic toujours
  **556/569** (13 net, inchangé), tous les autres types de gates EXACTS,
  `recorded` 9/9 (N0/N1/N2) OK.
- Première divergence de **type/coeffs** : row **40** (pas row 5 — la
  divergence de *wiring* à row 5-38 n'est qu'un artefact de cible de
  permutation en aval, cascadée par le déficit de 13 Generic ; rows 0-39
  = 40 gates `public_input`, byte-exact des deux côtés).

**Localisation précise du nouveau premier écart (row 40-73) — PAS un bug
snarky.** Ce bloc correspond au check de cohérence des feature-flags
(`assert_consistent`, wrap_main.ml ~301, 8 flags: range_check0/1,
foreign_field_add/mul, xor, rot, lookup, runtime_tables — cf. api.rs:493-505
qui les witnesse déjà comme `Boolean<Fq>` variables depuis `stmt[...]`, pas
des constantes). Comparaison coeff-à-coeff (outil labels) :
- Les FORMULES snarky sont byte-exactes vis-à-vis d'OCaml : `equal_constraints`
  (`cvar.rs:195`, R1CS `z_inv·z=1-r` puis R1CS `r·z=0`, labels `equals_1`/
  `equals_2`) et `Boolean::and` (`boolean.rs:89`, label `bool.and`) encodent
  bien un `a*b=c` via `m=1` — confirmé en comparant les POSITIONS de
  coefficient (`m` = index 3 d'un demi-generic) sur les rows qui matchent
  encore (ex. row 42-44, 47 : jsoo et rust identiques byte-à-byte).
- Sur les rows qui divergent (40, 41, 45…), le coefficient apparaît chez
  **rust en position `c` (constante, index 4) alors que jsoo le met en
  position `m` (index 3)** pour le même label logique — signe qu'un des
  trois opérandes (`a`,`b`,`c`) passés à `assert_r1cs` est un
  `FieldVar::Constant` côté rust là où OCaml le garde comme variable
  witnessée (et l'aurait matérialisée via `cached_constants`/`reduce_to_v`,
  cf. la note "Cause: OCaml reduce_to_v matérialise…" plus haut — même
  mécanisme que le déficit 500-1500, mais ici sur le bloc feature-flags,
  pas x_hat).
- **`assert_r1cs`/`assert_eq` (runner.rs:344-367) ne passent PAS par
  `reduce_to_var`/`cached_constants`** (ce mécanisme n'existe que dans
  `reduce_lincom`/`reduce_to_var`, constraint_system.rs:940-1058, utilisé
  pour les `scale`) : un `FieldVar::Constant` donné tel quel à `assert_r1cs`
  est plié directement dans le coefficient du gate plutôt que d'être
  matérialisé en variable + Equal, contrairement à OCaml qui matérialise
  systématiquement via `cached_constants` dès qu'une constante entre dans
  N'IMPORTE quelle contrainte (pas seulement `scale`).
- **Ce n'est donc PAS un bug de formule snarky** — mais MÉCANISME TROUVÉ,
  précisément localisé dans `cvar.rs::mul` (ligne 159-188) :
  ```rust
  (FieldVar::Constant(x), FieldVar::Constant(y)) => FieldVar::Constant(*x * y),
  (FieldVar::Constant(cst), cvar) | (cvar, FieldVar::Constant(cst)) => cvar.scale(*cst),
  (_, _) => { ... cs.assert_r1cs(...) ... }  // seul ce cas émet une contrainte
  ```
  Quand un des deux opérandes de `.mul()` est un `FieldVar::Constant`, rust
  optimise en `.scale()` **sans émettre AUCUNE contrainte** (juste une
  combinaison linéaire algébrique, repliée dans l'appelant). C'est ce chemin
  que prend `Boolean::and` (`boolean.rs:86`, `self.0.mul(&other.0, …)`) dès
  qu'un des deux booléens est `Boolean::false_()` = `FieldVar::zero()` — un
  `Constant`. Le bloc `assert_consistent` (api.rs:493-553) construit
  `table_width_at_least_1`/`lookups_per_row_4`/etc. via des chaînes de
  `Boolean::and`/`or`/`any` sur les 8 `feature_flags`, qui sont ici TOUS
  witnessés à `false` (circuit minimal, pas de lookup/range-check/xor/rot) —
  donc de nombreux `.mul()` internes tombent sur le cas
  `(Constant(0), var)`/`(var, Constant(0))` et **disparaissent silencieusement**
  côté rust, alors qu'OCaml (dont le `Snark.Run`/`Cvar` matérialise les
  constantes plus tôt, cf. `cached_constants`/`reduce_to_v` déjà documenté
  plus haut pour x_hat/500-1500) émet un R1CS réel à chaque `and`/`or`, quel
  que soit le statut constant d'un opérande. C'est la cause du bloc
  `equals_1`/`equals_2` divergent en row 40-73 : pas un bug de formule, un
  écart de **stratégie d'optimisation** (constant-folding précoce côté rust
  vs matérialisation systématique côté OCaml).
  ⚠️ **Ne PAS "corriger" `cvar::mul` en général** (retirer l'optimisation
  casserait probablement d'autres compteurs de gates ailleurs, potentiellement
  en mieux ou en pire — c'est une piste à tester isolément, pas un patch
  aveugle). Prochaine étape concrète et à faible risque : dans le bloc
  `assert_consistent` d'api.rs (493-553) UNIQUEMENT, remplacer les opérandes
  `Boolean::false_()`/les flags connus constants par des variables
  witnessées explicitement (comme fait pour `vk_digest`/`messages` cette
  session) avant de les passer à `Boolean::and`/`or`/`any`, pour forcer
  l'émission des mêmes R1CS qu'OCaml sans toucher `cvar.rs`. Mesurer avec
  le tool de labels après ce changement isolé ; si concluant, envisager
  seulement alors un changement plus général dans `cvar::mul`/`cached_constants`.

**Essai fait et REVERTÉ — `lookup_pattern_range_check` en chaîne `.or()`.**
Lecture directe d'OCaml (`~/Projects/mina/src/lib/crypto/kimchi_backend/common/plonk_types.ml:263-320`,
`Features.to_full`) : `lookup_pattern_range_check = range_check0 ||| range_check1 ||| rot`
est un chaînage `or_` PLAT (2×`.or()`), alors que `table_width_at_least_1`/
`lookups_per_row_4` passent bien par le combinateur `any` (`~any:(fun x -> lazy
(B.any …))`, donc bien `Boolean.any`). Notre api.rs (ligne ~507) utilisait
`Boolean::any(&[range_check0,range_check1,rot])` (3 arguments) pour LES
DEUX cas — hypothèse : `lookup_pattern_range_check` devrait utiliser
`.or().or()` au lieu de `any`. **Testé, RÉGRESSE fortement** : Generic
556→**555**, divergence 2869→**3844**. Reverté immédiatement (diff propre,
retour confirmé à 2869). Donc soit l'hypothèse de lecture est incorrecte
(peut-être que le vrai `Boolean.any` OCaml pour 3 args EST algébriquement
équivalent à `sum.equal(zero)` et produit le même gate qu'un `or` chaîné one
optimisé différemment côté kimchi — soit la divergence row-40 ne vient PAS
de ce site précis du tout (l'attribution au bloc `assert_consistent` était
une corrélation de position, pas une preuve directe — aucune capture
`SNARKY_LOG_CONSTRAINTS` n'a authentifié que jsoo rows 40-73 EXECUTENT bien
`Plonk_types.Features.to_full`/`assert_consistent`, seulement une
coïncidence de comptage de rows). **Ne pas réessayer cette piste sans
d'abord obtenir une capture jsoo authentifiant précisément quelle fonction
OCaml émet les rows 40-73** (le log `SNARKY_LOG_CONSTRAINTS` capturé cette
session, `/tmp/claude-1000/wraplog2.txt`, ne contenait pas de marqueurs
`wrap_main.ml`/`assert_consistent` autour de cette région — l'instrumentation
de labels actuelle ne couvre que le côté RUST, pas jsoo à ce niveau de
détail ; il faudrait ajouter des labels OCaml explicites ou recouper avec
les line numbers du fichier comme fait plus haut pour `choose_key`).

## Localisation AUTHENTIFIÉE de row 40 (via labels file:line rust + lecture OCaml) — 2026-07-12

**Contrairement à l'hypothèse précédente (assert_consistent/feature-flags),
row 40 (dump) = log_row 0 vient du bloc `forbidden_shifted_values` (`Wrap.Other_field.check`),
PAS du bloc feature-flags.** Vérifié en capturant `SNARKY_LOG_CONSTRAINTS=1`
côté rust avec labels `file:line` (`/tmp/claude-1000/rustlog.txt`, dump_row =
log_row + 40, confirmé par `api.rs:416 equals_1` au tout début du dernier
bloc `^0:`) : log rows 0-32 → `api.rs:413-423` (boucle `forbidden` × 5 slots
`[cip,b,zsl,zds,perm]` en ordre inverse) ; log row 33 → `api.rs:430`
(`which_branch.equal`) ; log rows 35-38 → `api.rs:472` (**feature flag
bit**, i.e. le bloc feature-flags ne commence qu'à **dump row 75**, PAS 40).

**CAUSE RACINE TROUVÉE (source OCaml lue directement,
`~/Projects/mina/src/lib/crypto/pickles/impls.ml:91-102`,
`Other_field.check`) :**
```ocaml
let equal (x1, b1) (x2, b2) =
  let%bind x_eq = Field.Checked.equal x1 (Field.Var.constant x2) in
  let b_eq = match b2 with true -> b1 | false -> Boolean.not b1 in
  Boolean.( && ) x_eq b_eq
in
Checked.List.map (Lazy.force forbidden_shifted_values) ~f:(equal t)
>>= Boolean.any >>| Boolean.not >>= Boolean.Assert.is_true
```
`Impls.Wrap.Other_field.t = Field.t * Boolean.var` — **(low bits, high
bit)**, PAS un simple `Field.t`. Le Fp (Tick, ~255 bits) ne rentre pas
losslessly dans un seul élément Fq (Tock, ~254 bits) ; OCaml représente donc
chaque valeur déférée (`cip`, `b`, `zsl`, `zds`, `perm`) comme une PAIRE
(bas + bit haut), et chaque comparaison à une valeur interdite compare
**LES DEUX composantes** (`x_eq` ET `b_eq`, combinés par un `Boolean.&&`
— un R1CS `bool.and` en PLUS des 2 R1CS `equal_constraints` par valeur
interdite). **Notre `stmt[0..5]` (api.rs:387-391) sont de simples
`FieldVar<Fq>` SANS bit haut séparé** — `forbidden_shifted_values_fq()`
(shifted_value.rs:172) recolle tout dans une seule valeur Fq, donc notre
boucle (api.rs:413-423) ne compare QUE la valeur, jamais un bit haut → il
manque structurellement un `bool.and` par valeur interdite testée, et
potentiellement toute la construction du statement (`stmt[0..5]`) est
LOSSY/simplifiée par rapport au layout OCaml réel (qui a un slot de bit
haut séparé quelque part dans le statement public wrap).

**NE PAS PATCHER À L'AVEUGLE** (ex. ajouter un `bool.and` avec une valeur
bidon) : `cvar::mul` replie tout produit par une `Constant` (voir plus haut)
donc un faux bit ne produirait même pas la contrainte recherchée. Le
vrai fix nécessite : (1) retrouver où/si le bit haut de `cip`/`b`/`zsl`/
`zds`/`perm` existe déjà ailleurs dans le statement wrap (40 slots, cf.
`o1js-to-zkvm/crates/pickles-verifier/src/deferred.rs::wrap_public_input`
et le layout `composition_types` OCaml `Wrap.Statement.to_data`), sinon (2)
l'AJOUTER au layout (potentiellement rupture de layout public input, à
faire avec grand soin et en vérifiant `public_input_size` reste 40 des
deux côtés). C'est un travail de restructuration du statement, pas un
patch local de la boucle forbidden — prochaine étape prioritaire pour
fermer row 40 et probablement une bonne partie du reste (556 vs 569
Generic).

**CORRECTION IMMÉDIATE (même session) — hypothèse top-bit RÉFUTÉE.**
`impls.ml:50` (`type t = Field.t * Boolean.var`, avec le `bool.and`) est le
`Other_field` du module **Step** (Tock-in-Tick, PAS notre cas). Le
`Other_field` du **Wrap** (Tick-in-Tock, notre cas) est à `impls.ml:187` :
```ocaml
module Other_field = struct
  module Constant = Tick.Field
  type t = Field.t   (* PAS de paire, PAS de bit haut *)
  let check t =
    let equal x1 x2 = Field.Checked.equal x1 (Field.Var.constant x2) in
    Checked.List.map (Lazy.force forbidden_shifted_values) ~f:(equal t)
    >>= Boolean.any >>| Boolean.not >>= Boolean.Assert.is_true
end
```
C'est EXACTEMENT ce que fait notre boucle rust (api.rs:413-423) — simple
comparaison de valeur, `Boolean.any`, `not`, `assert is_true`. **Aucun bit
haut manquant côté wrap.** Ne pas réessayer cette piste.

**Nouvelle piste, non résolue — écart de CARDINALITÉ dans le comptage
observé.** `forbidden_shifted_values_fq()` (rust) retourne **2** valeurs
(vérifié par test temporaire). Avec 5 slots × 2 valeurs interdites, on
attend 5×2=10 appels `equal()` = 20 R1CS (equals_1+equals_2, 10+10). Or le
comptage réel des labels dans le dump rust pour log rows 0-32 (le bloc
`forbidden`, 33 lignes) donne **32 equals_1 / 20 equals_2 / 15 bool.and /
1 assert equals** — largement AU-DESSUS de 10+10, plutôt cohérent avec
~26 appels `equal()` (donc ~5.2 valeurs interdites par slot, pas 2) et
15 `bool.and` (incohérent avec `Boolean::any(2 items)` qui ne devrait
produire qu'1 `.or()`/slot = 5 `bool.and` total, pas 15). **Hypothèses à
vérifier avant tout nouveau patch** (prochaine étape, PAS encore faite) :
1. Le nombre exact de `forbidden_shifted_values` côté OCaml (`Tick.Field`
   modulus, `size_in_bits`) pourrait différer de 2 — recompter via
   `~/Projects/mina` directement (script OCaml ou lire les constantes) ;
2. Notre appel réel dans la boucle `for slot in stmt[0..5].rev() { for
   value in &forbidden { ... } }` (api.rs:413-416) pourrait ne PAS
   utiliser `forbidden_shifted_values_fq()` mais une variante différente
   — À VÉRIFIER en relisant l'import exact ligne 408 (`crate::shifted_value::
   forbidden_shifted_values_fq()`) et en s'assurant qu'aucune autre
   fonction similaire n'est utilisée ailleurs et confondue dans le comptage
   de labels (le fenêtrage log rows 0-32 pourrait chevaucher un autre bloc
   voisin, à re-vérifier avec le tool de labels précisément borné).
3. Ne pas conclure sans avoir d'abord recompté proprement des DEUX côtés
   (rust ET jsoo) le nombre exact d'appels `equal()`/`Field.Checked.equal`
   dans ce bloc précis, avec la même méthode qu'utilisée pour authentifier
   row 40 (labels file:line rust + recoupement jsoo `SNARKY_LOG_CONSTRAINTS`
   avec labels de fichier — actuellement seul le côté rust a des labels
   file:line utilisables ; jsoo n'a pas toujours de `File "..."` sur ces
   lignes `impls.ml` génériques, à vérifier).

**MISE EN GARDE MÉTHODO — le texte `SNARKY_LOG_CONSTRAINTS` n'est PAS fiable
pour compter les occurrences dans une fenêtre.** Vérifié empiriquement :
un compteur runtime (`eprintln!` direct dans la boucle `forbidden`,
retiré après usage) montre que le corps `{ for slot in stmt[0..5] {...} }`
s'exécute **4 fois** au total pendant un run complet (`forbidden.len()=2`,
`eqs.len()=2` à chaque fois, stable) — mais le texte log attribue **15**
occurrences du label `api.rs:419` (`any`) à une seule fenêtre de 33 lignes
qui semblait correspondre à un seul dump (`^0:` unique), alors que la
théorie (5 slots × 1 `any()` par slot) n'en prédit que 5. Cet écart montre
que **plusieurs exécutions du circuit sont concaténées dans le même bloc
`^0:` numéroté** (compilation + génération de witness + éventuels passes
bootstrap du "two-pass" dump, cf. `prove_base_case_two_pass`), invalidant
tout comptage de MULTIPLICITÉ tiré du texte log au sein d'une fenêtre —
seule l'IDENTIFICATION de la PREMIÈRE ligne d'un segment (`dump_row =
log_row + 40`) reste fiable, pas le nombre d'occurrences dans la fenêtre.
**Utiliser les dumps JSON (`wrap-circuit-{jsoo,rust}.json`) pour tout
comptage — jamais le texte log.**

## RÉSULTAT CLEF — le déficit Generic (556 vs 569) NE VIT PAS avant row 543

Comptage FIABLE (JSON dumps, pas le texte log) du nombre de gates `Generic`
par fenêtre de rows, jsoo vs rust :
```
0-40: 40=40   40-75: 35=35   75-100: 25=25   100-180: 80=80
180-231: 51=51   231-300: 5=5   300-543: 19=19   (TOUS EXACTS)
543-700: jsoo=5   rust=90   (rust +85)
700-1024: jsoo=103 rust=24  (rust -79, net range 543-1024 : rust +6)
```
**Row 40 (et tout le bloc `forbidden`/`choose_key`/VK on-curve/1er sponge,
rows 0-542) a un DÉCALAGE DE TYPE/COEFFS/WIRING (ordre d'encodage différent,
cf. position `m` vs `c` documentée plus haut) MAIS UN COMPTE GENERIC
IDENTIQUE aux deux côtés.** Autrement dit : même si on résolvait
parfaitement la divergence de row 40, ça ne fermerait PAS le déficit
Generic 556→569 (13 net) — seulement une partie du compteur cosmétique
"divergent rows" (2869). **Ne plus prioriser row 40 pour fermer le
compteur Generic.**

**LOCALISATION PRÉCISE ET MÉCANISME du vrai déficit — row 594-657.**
Comparaison type-par-type (JSON dumps) : jsoo et rust matchent EXACTEMENT
jusqu'à row 595 (un point on-curve check partagé, labels rust
`checked_mul`/`on-curve x^2`/`on-curve check` — le premier point `lr`/
`openings`). **À row 596, jsoo bascule vers `CompleteAdd`/`VarBaseMul`**
(début du fold bulletproof, scalar-mult du premier round IPA) **alors que
rust CONTINUE À FAIRE DES ON-CURVE CHECKS PURS jusqu'à row 657** (64 rows
consécutives, ~43 points vérifiés on-curve d'affilée, tous avec le même
label `checked_mul/on-curve x^2 + on-curve check/on-curve check`) avant de
passer à autre chose (`equals_1` à row 658).

**Mécanisme identifié** : notre `openings.lr` est construit par une boucle
UNIQUE `for &(l,r) in &w.lr { lr.push((mkpt(sys,l)?, mkpt(sys,r)?)); }`
(api.rs:654-657) qui witnesse+checke on-curve TOUS les points lr (jusqu'à
`ROUNDS` paires) d'un coup, PUIS le fold bulletproof
(`bulletproof.rs::bullet_reduce_terms`, appelé plus tard depuis `verify`,
PARTAGÉ step/wrap) itère sur ce vecteur déjà complet pour plier
séquentiellement (`endo`/`endo_inv`/`add_fast` par paire). **OCaml
interleave au contraire check-on-curve-de-la-paire PUIS fold-de-la-paire,
round par round** (check l, check r, fold immédiatement dans l'accumulateur,
passer au round suivant) — d'où son passage à `VarBaseMul` dès row 596
alors que nous groupons tous les checks avant de plier.

**Risque du fix — `bullet_reduce_terms` est appelé depuis `verify`
(step_verifier.rs), PARTAGÉ avec le step (FULL MATCH).** `lr`/
`prechallenges` de `bullet_reduce_terms` (Point<F>, déjà witnessé) sont
DÉCOUPLÉS du calcul des `prechallenges` eux-mêmes (`bullet_reduce_challenges`,
opère sur un TYPE DIFFÉRENT `PointVar<F>`, probablement en amont dans
`oracles.rs`) — donc les prechallenges ne dépendent PAS de l'ordre de
witnessing des points `Point<F>` finaux, ce qui rend l'interleaving
FAISABLE EN THÉORIE (fusionner la boucle `mkpt` de api.rs avec le fold de
`bullet_reduce_terms`, en passant des points DÉJÀ pliés à `verify` au lieu
d'un vecteur `lr` brut). **MAIS `verify`/`bullet_reduce_terms` sont
partagés avec le step** → il faut soit (a) faire cet interleaving
UNIQUEMENT côté wrap (dupliquer un chemin `bullet_reduce_terms_wrap` ou
passer un point déjà-plié en paramètre de `verify` au lieu du vecteur brut,
sans toucher au chemin step), soit (b) vérifier que réordonner
`bullet_reduce_terms` lui-même reste neutre pour le step (peu probable vu
son FULL MATCH actuel, donc option (a) plus sûre). **NE PAS toucher
`bullet_reduce_terms`/`verify` sans dupliquer le chemin ou vérifier
`rust-pickles-step-gates-diff.ts` reste FULL MATCH après coup.** C'est le
prochain chantier concret et prioritaire (plus prometteur que row 40, car
il touche potentiellement les 13 Generic ET une bonne partie des ~2500
rows encore divergentes dans 543-4096).

**APPROFONDISSEMENT (même session) — l'interleaving est PLUS dur que
prévu : PAS une simple fusion de boucles.** Tracé le call-graph exact :
`openings.lr` (déjà on-curve-checké dans api.rs via `mkpt`) est consommé
DANS `incrementally_verify.rs::incrementally_verify_proof` (= le `verify`
partagé step/wrap, step_verifier.rs:50) à DEUX endroits :
1. `ipa_challenges_transcript` (ligne ~279) — dérive les `prechallenges`
   en absorbant L/R dans le sponge round par round (nécessite l'état du
   sponge déjà avancé par tout le protocole précédent : beta/gamma/alpha/
   zeta/fork) ;
2. `bullet_reduce_terms` (ligne ~293) — plie `lr` avec ces `prechallenges`.

**Les `prechallenges` ne peuvent PAS être calculés avant d'entrer dans
`verify`** (ils dépendent de l'état du sponge partagé, construit
progressivement PENDANT `verify`). Donc on ne peut pas simplement
pré-plier `lr` en dehors de `verify` et ne passer qu'un point déjà réduit —
il faudrait déplacer le CHECK on-curve LUI-MÊME à l'intérieur de la boucle
`ipa_challenges_transcript`/`bullet_reduce_terms`, DANS le fichier
partagé step/wrap. Ce n'est donc PAS un simple réordonnancement côté
api.rs (wrap-only) mais une modification du cœur `verify` partagé,
paramétrée pour ne changer que le chemin wrap (ex. un flag / une variante
`check_lr_inline: bool`, ou dupliquer `bullet_reduce_terms` en
`bullet_reduce_terms_with_check` appelé uniquement par le wrap). **Risque
réel de casser le step FULL MATCH si mal isolé — TOUJOURS vérifier
`rust-pickles-step-gates-diff.ts` reste FULL MATCH après toute modif de
`incrementally_verify.rs`/`bulletproof.rs`, en plus de `recorded`
(N0/N1/N2).** Pas tenté cette session (trop risqué pour un essai non
vérifié en profondeur) — c'est la tâche prioritaire pour la prochaine
session, avec ce chemin de fichiers déjà identifié précisément.

## Essai FAIT et REVERTÉ — `bullet_reduce_interleaved` (session suivante, même jour)

**Implémenté intégralement** (compile, mathématiquement correct, testé) :
- `bulletproof.rs::bullet_reduce_interleaved` — nouvelle fonction qui fusionne
  `ipa_challenges_transcript` + `bullet_reduce_terms` en UNE boucle par round
  (check L/R on-curve → absorb L,R → squeeze prechallenge → fold immédiat),
  au lieu de deux passes séparées.
- `incrementally_verify_proof`/`step_verifier::verify`/`verify_one`/
  `step_main` : nouveau paramètre `on_curve_coeffs: (F,F)` fileté à travers
  toute la chaîne jusqu'à `wrap_main.rs`/`step_main.rs` (les 2 call sites
  réels, `(F::from(0),F::from(5))` pour Pasta).
- `api.rs` : `lr` witnessé SANS check on-curve upfront (`mkpt_unchecked`),
  le check se fait maintenant dans `bullet_reduce_interleaved`.

**Risque `verify_one`/step vérifié RÉEL et CONFIRMÉ, pas hypothétique** :
`recursive_per_proof_input` (recursive_step.rs) → `circuit()` →
`step_main::<Fp,PallasParameters>` → `verify_one` → `verify` →
`incrementally_verify_proof` EST le chemin live de `recorded_n1_cycle`/
`recorded_n2_cycle` (pas mort comme je le pensais initialement — trouvé
via l'erreur de compilation sur l'arité de `verify_one`, PAS par grep
naïf qui ratait l'appel `::<PREV_ROUNDS, WRAP_ROUNDS>`). Découverte
positive en chemin : le `mkpt` de `recursive_per_proof_input` pour
`lr`/`messages`/`openings` NE FAISAIT DÉJÀ AUCUN check on-curve (gap
préexistant, hors scope, non traité) — donc mon changement n'a RIEN
régressé côté step sur ce point précis.

**Résultat des tests** :
- `cargo test -p pickles --release --test recorded` : **9/9 PASS**
  (N0/N1/N2 tous verify correctement — la maths de l'interleaving est
  saine, le fold donne bien le même résultat qu'avant).
- `rust-pickles-step-gates-diff.ts` : **STEP GATES: FULL MATCH** inchangé
  (le chemin `recursive_per_proof_input`/`verify_one` n'est PAS exercé
  par le test de parité de gates step lui-même, qui ne couvre que le
  circuit minimal ; seul `recorded_n1/n2` l'exerce, et ces tests passent
  fonctionnellement mais leur PARITÉ DE GATES n'a pas de test dédié —
  donc `verify_one` a pu changer de structure sans qu'aucun test actuel
  ne le détecte).
- `rust-pickles-wrap-gates-diff.ts` : **RÉGRESSION** — divergence
  **2869 → 3524**, Generic **556 → 541** (s'éloigne de la cible 569 au
  lieu de s'en rapprocher). Reverté proprement (`git checkout` sur les 6
  fichiers touchés), rebuild napi, ré-confirmé 2869/556 restauré, 9/9
  recorded re-vérifié sur l'état reverté.

**Pourquoi ça a régressé malgré une implémentation fidèle à OCaml en
apparence** : l'interleaving change l'ORDRE D'ABSORPTION DANS LE SPONGE
lui-même n'a PAS changé (toujours absorb L puis R par round, comme avant)
— mais le fait de check on-curve JUSTE AVANT d'absorber, plutôt qu'en
amont, change quels FieldVar sont déjà "seal"és/réduits au moment de
l'absorption, ce qui modifie le PAIRING double-generic en aval de façon
plus large que prévu (3524 diverge sur BEAUCOUP plus de rows que 2869,
type=2755 contre ~1900 avant). Root-cause probable : le point de départ
(row 596 dans l'AVANT) n'était peut-être pas le SEUL endroit où rust
batch les checks — en changeant seulement `lr`, on a désynchronisé son
alignement avec d'autres séquences (VK, messages, sg_olds) qui, elles,
restent batchées à l'ancienne — la fenêtre 231-543 qui était PARFAITEMENT
alignée avant (voir plus haut, comptage Generic exact par fenêtre)
casse probablement aussi avec ce changement (non re-mesuré en détail
avant de revert, faute de temps).

**Leçon pour la suite** : ne pas interleaver `lr` seul. Si on retente,
il faut soit (a) interleaver TOUT le bloc consommateur de points
(messages/sg_olds/lr/VK on-curve) de façon cohérente avec jsoo dans le
MÊME mouvement, soit (b) re-mesurer avec le comptage par fenêtre
(technique de cette session, cf. "RÉSULTAT CLEF" plus haut) AVANT de
conclure, pour voir PRÉCISÉMENT quelle fenêtre a régressé et pourquoi,
plutôt que revert dès la première mesure globale défavorable — on a
peut-être raté un gain partiel (ex. la fenêtre 543-700 pourrait s'être
améliorée même si le total a empiré). Prochaine tentative : mesurer par
fenêtre AVANT de décider revert/keep, pas seulement le total.

**FAIT (re-tenté même session) — comptage par fenêtre AVANT de revert,
confirme un signal mitigé, pas un simple raté.** Ré-appliqué l'identique
changement (mêmes 6 fichiers) pour obtenir les dumps JSON avant de
conclure. Comptage Generic par fenêtre, AVANT (2869, référence) vs APRÈS
(3524, ce essai) :
```
fenêtre      avant(excès rust)   après(excès rust)
543-700      jsoo=5  rust=90 (+85)   jsoo=5  rust=28 (+23)   ← AMÉLIORATION nette
700-1024     jsoo=103 rust=24 (-79)  jsoo=103 rust=27 (-76)  ← quasi inchangé
1024-2048    rust -34                rust -37                ← légère régression
2048-4096    rust +29                rust +30                ← quasi inchangé
4096-8192    rust -14                rust +32                ← RÉGRESSION nette (swing de 46)
```
**Conclusion ferme** : l'interleaving `lr` seul RÉSOUT bien une partie du
problème qu'il ciblait (543-700 : +85→+23, la sur-émission qu'on avait
identifiée est bien réduite aux 2/3) — la théorie du mécanisme était
CORRECTE. Mais il introduit une régression NOUVELLE et plus grosse en
aval (4096-8192, +46) qui n'a pas de lien évident avec `lr` — signe que
le déplacement du point de fold change le competing timing d'un autre
composant (le nombre total de rows utilisées avant un certain point
déplace le domaine/curseur d'une passe ultérieure : ft_comm, finalize,
ou l'évaluation z1/z2/Other_field qui vient juste après `openings` dans
api.rs). Reverté à nouveau (6 fichiers, `git checkout`), re-confirmé
2869/556 et 9/9 recorded sur l'état reverté. **Le prochain qui retente
cette piste doit d'abord identifier CE QUI dans la région 4096-8192
dépend du nombre de rows émises en amont** (probablement un `ft_comm`/
`finalize` dont les positions de padding/domaine sont sensibles au
compte total de Generic déjà émis) avant de retoucher `lr`.

**Vérifié (session suivante) — ce n'est PAS `combine_commitments`.**
Hypothèse testée : peut-être `combine_commitments` (le fold Horner des
~40 commitments VK/messages/sg_old/x_hat, lignes 231-543) a besoin du
même traitement interleaved que `lr`, et c'est ça qui manque. **Réfuté
par la donnée** : re-mesuré cette même fenêtre (0-543) AVEC le patch
`bullet_reduce_interleaved` appliqué → **toujours exact des deux côtés**
(236=236 sur 0-300, 19=19 sur 300-543), inchangé par rapport au 2869
baseline. Donc `combine_commitments`/VK/messages ne sont PAS en cause et
n'ont pas besoin d'un traitement analogue — la régression 4096-8192
(-14→+32 avec le patch lr) est un pur EFFET DE CASCADE en aval (le total
de rows générique déplacé en amont décale quelque chose de sensible
plus loin dans le circuit), pas un second bug indépendant qu'on
pourrait corriger "en même temps". Root cause de la cascade toujours
NON identifiée (candidats plausibles : `finalize_deferred`, `ft_comm`,
ou `check_bulletproof_equation`/`scale_fast` juste après le fold — tous
consomment des valeurs qui dépendent indirectement du layout amont).
**Reverté à nouveau** (mêmes 6 fichiers), re-confirmé 2869/556 et 9/9
recorded.

**Conclusion de cette 2e passe** : la piste `lr` interleaved seule est
définitivement insuffisante ET son échec n'est pas "réparable" par un
fix ponctuel ailleurs trouvé jusqu'ici — les deux régions qui matchaient
déjà parfaitement (0-543) n'ont pas besoin de retouche. Le vrai
prochain pas est d'INSTRUMENTER la cascade elle-même : comparer
précisément row par row 4096-5376 avec les labels (comme fait pour
row 40 et row 594) pour identifier QUELLE fonction précise réagit au
décalage, plutôt que deviner (ft_comm/finalize étaient des hypothèses
non vérifiées cette session, faute de temps).

## Session — jsoo label instrumentation attempt (2026-07-12/13)

**Bug fix RÉEL et VALIDÉ (indépendant de l'objectif labels)** : le bundle
jsoo (`o1js_node.bc.cjs`) ne pouvait plus être reconstruit du tout depuis
l'état actuel des sources — `npm run build:jsoo:node` échouait avec 3+
erreurs de type (`wrap.ml:115`, `step.ml:480/491/900`, `pickles.ml:1079/1273`)
: `p_eval_1`/`p_eval_2` (Tick.Oracles) retournent désormais un `array`
(support multi-chunk) là où ces sites faisaient encore
`[| p_eval_1 o |]` (double-wrap). **Confirmé PRÉEXISTANT** (même échec avec
mes modifs stashées). Corrigé en retirant le wrap redondant aux 6 sites où
c'était un vrai bug (`wrap.ml:115`, `step.ml:480,491,900`, `pickles.ml:1079,1273`),
et en mettant à jour `X_hat.t` (step.ml, local à `expand_proof`) de
`Tock.Field.t Double.t` vers `Tock.Field.t array Double.t` pour rester
cohérent avec le flux array désormais uniforme. **`proof.ml` (`of_repr`) a
délibérément GARDÉ son wrap** — ce n'est PAS le même bug : c'est une
conversion Stable.V1 (scalaire, sérialisé sur disque) → live (array), le
wrap y est correct et nécessaire (à ne pas retoucher).

**Validation** : `dune build src/mina/src/lib/crypto/pickles/` exit 0 ;
jsoo bundle rebuild réussi ; `rust-pickles-wrap-gates-diff.ts` donne
EXACTEMENT 2869/556 (identique à avant le fix, confirmant neutralité
sémantique) ; `rust-pickles-step-gates-diff.ts` toujours FULL MATCH.
**Ce fix mérite d'être committé séparément dans le submodule o1js/mina —
il débloque TOUT travail OCaml futur sur ce repo**, indépendamment des
labels.

**Objectif labels jsoo — implémenté mais NE MARCHE PAS pour la raison
attendue.** Ajouté `snarky_intf/constraint_label_debug.ml` (ref global +
flag env), threadé un champ `label` dans `Gate_spec.t`
(`kimchi_pasta_snarky_backend/plonk_constraint_system.ml`), à travers
`add_row`/`add_generic_constraint`/le flush du pending generic/le public
input, et un export `GATE_LABEL <row>: <label>` en fin de
`finalize_and_get_gates` (miroir exact du mécanisme rust
`GateSpec.label`/`gate_labels()` de `3409b070ed`). **Compile proprement,
gate-neutre (vérifié : dump identique 2869/556 avant/après)**.

**MAIS : `finalize_and_get_gates` n'est JAMAIS appelé pendant le compile
réel utilisé par `rust-pickles-wrap-gates-diff.ts`.** Vérifié avec des
`Printf.printf`/`Stdlib.prerr_endline` inconditionnels à 3 niveaux :
`finalize_and_get_gates` lui-même, et `Impls.{Step,Wrap}.Keypair.generate`
(qui d'après la lecture statique du code — `cache.ml:124/267` →
`Keypair.generate` → `Tick/Tock.Keypair.create` = `Dlog_plonk_based_keypair.create`
→ `Inputs.Constraint_system.finalize_and_get_gates` — DEVRAIT être sur le
chemin) : **aucun des 3 print ne s'affiche**, alors que le compile
RÉUSSIT et produit des bytes de wrap-pk corrects (le test entier
fonctionne). Donc le vrai chemin de compilation utilisé par
`Program.compile()` d'o1js N'EST PAS celui que la lecture statique du
code suggère — soit un cache (`Key_cache.Sync.read`, mais `cache=[]` par
défaut dans `compile.ml:1038`, donc improbable), soit une exécution dans
un contexte (worker/thread jsoo `Promise.run_in_thread`) dont le
stdout/stderr n'est pas capturé par notre pipe, soit une toute autre
fonction de compilation plus récente que je n'ai pas trouvée. **Piste
`Promise.run_in_thread`** (utilisé ailleurs, ex.
`plonk_dlog_proof.ml:batch_verify`) **la plus probable mais NON
confirmée** — pas eu le temps de vérifier si jsoo mappe ça sur un vrai
`worker_threads.Worker` (il y en a dans `node-backend.js:107`, mais pour
des workers WASM/Rust multi-thread, pas manifestement pour OCaml/jsoo).

**Prochaine étape concrète (non faite)** : soit (a) trouver la VRAIE
fonction de compilation OCaml appelée par `Program.compile()`
(chercher differently — tracer depuis le binding jsoo_exports plutôt que
depuis `cache.ml`/`impls.ml` en lecture statique, ou binary-search avec
des prints à des points de plus en plus profonds en partant du binding
JS d'entrée), soit (b) confirmer/infirmer l'hypothèse
`Promise.run_in_thread`/stdout-non-capturé (essayer de rediriger stderr
différemment, ou chercher un moyen de forcer une exécution synchrone),
soit (c) abandonner l'approche OCaml-side label et se rabattre sur une
méthode de corrélation différente (ex. comparer les MULTI-SETS de
coefficients/types entre jsoo et rust sans labels, ou instrumenter côté
RUST/WASM kimchi si c'est bien là que la finalisation a lieu réellement).

**État du repo** : tous les fichiers OCaml modifiés sont dans
`o1js/src/mina` (submodule) et `o1js/src/mina/src/lib/snarky` (submodule
imbriqué) — PAS COMMITÉS (git status propre à committer, rien de perdu,
un `git stash@{0}` existe dans `src/mina` avec de l'état préexistant non
lié à ce travail, à ne pas drop sans vérifier). Le jsoo bundle actuel
(`src/bindings/compiled/node_bindings/o1js_node.bc.cjs`) intègre TOUS ces
changements (build fix + label plumbing inutilisé) et est vérifié
fonctionnellement identique (2869/556, step FULL MATCH, 9/9 recorded côté
rust inchangé).
