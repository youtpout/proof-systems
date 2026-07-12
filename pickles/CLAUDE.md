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
