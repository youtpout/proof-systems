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

### Branche expérimentale `wrap-iso-rewrite`

La branche `wrap-iso-rewrite` porte une réécriture structurelle assumée du
wrap. Elle ne doit pas être comparée aux mesures de parité de `pickle-rs`
avant la fin du réordonnancement : les régressions transitoires du wrap sont
attendues. Le step reste inchangé et FULL MATCH.

Premier lot appliqué : l'API alloue désormais les `openings` avant les
`messages`, puis calcule le digest de VK immédiatement avant l'entrée dans le
transcript de vérification. Cela reproduit l'ordre de haut niveau de
`wrap_main.ml`/`wrap_verifier.ml`; le déplacement des `prev_proof_state` et
des `unfinalized` reste à effectuer comme bloc atomique avant de retester la
parité wrap.

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

**DIRECTIVE UTILISATEUR (2026-07-13) : l'OCaml est fonctionnel, NE PLUS LE
MODIFIER.** Tout le travail d'instrumentation jsoo ci-dessus a été
ENTIÈREMENT REVERTÉ : `checked_runner.ml` restauré à son état
`SNARKY_LOG_CONSTRAINTS` préexistant-avant-cette-session (pas HEAD — HEAD
n'a même pas cette instrumentation, elle était déjà en dirty state avant
que je commence) ; `wrap.ml`/`step.ml`/`pickles.ml`/`plonk_constraint_system.ml`
restaurés à HEAD (`git checkout HEAD --`, pas `git checkout --` seul —
piège rencontré : ce dernier restaure depuis l'INDEX si le fichier y est
staged, pas depuis HEAD) ; `constraint_label_debug.ml` supprimé. Le
bundle jsoo compilé (non tracké par git, `.gitignore`) reste sur le
DERNIER BUILD RÉUSSI (avec le fix p_eval array — un `dune build` qui
échoue ne touche pas l'artefact précédent) — vérifié fonctionnellement
neutre (2869/556 + step FULL MATCH identiques au comportement attendu).
**NE PLUS RECOMPILER LE JSOO, ne plus toucher AUCUN fichier OCaml.** Toute
la suite du travail de parité de gates reste 100% côté RUST
(proof-systems), en utilisant le dump jsoo existant comme référence figée.

## TRIANGULATION du root cause profond (2026-07-13, rust-only)

Sur l'état de référence 2869 (baseline, PAS l'interleaving), comptage par
fenêtre de 128 rows sur toute la région 1024-8192 : divergences
concentrées en 3 zones (1024-1280 : rust −36 ; 2048-2176 : rust −30 ;
3584-3712 : rust +35), puis un bruit résiduel diffus et alterné partout
ailleurs (±1 à ±3, cohérent avec une PROPAGATION en aval d'un décalage
originel, pas des bugs indépendants).

**Zone 1024-1070 inspectée en détail** : mélange `EndoMulScalar`/`Poseidon`
des deux côtés, mêmes comptes totaux sur la fenêtre 1000-1100
(EndoMulScalar 40=40, Poseidon 41 vs 46 — proche) **mais ORDRE différent** :
jsoo fait une longue série `EndoMulScalar` PUIS bascule sur `Poseidon` ;
rust fait l'inverse (`Poseidon` d'abord, `EndoMulScalar` après), avec un
chevauchement partiel entre les deux.

**Zone 3575-3625 inspectée en détail** (bloc `EndoMul`, la boucle Horner de
`combine_commitments` sur les ~46 commitments `sg_old/x_hat/ft_comm/z_comm/
generic/psm/complete_add/mul/emul/endomul_scalar/w_comm[15]/coefficients[15]/
sigma_init[6]`) : les DEUX interruptions `add_fast` de rust (rows 3582 et
3597, séparées de 15 rows = 1 item) tombent à des endroits où jsoo continue
tout droit en `EndoMul` — jsoo interrompt son propre chemin `EndoMul` PLUS
TARD et MOINS SOUVENT dans cette fenêtre (une seule interruption visible
contre deux côté rust) : signe que jsoo regroupe/scale plusieurs items
différemment (peut-être un ordre de traitement légèrement différent des 15
`w_comm`/`coefficients`, ou un point de départ décalé dans la liste).

**Conclusion : 3 angles indépendants (row-40 déjà documenté = encodage
double-generic ; row 594 = check-on-curve batché vs interleaved du
bulletproof ; row 1024 = squeeze Poseidon batché vs interleaved avec la
conversion EndoMulScalar ; row 3582 = Horner `combine_commitments`
légèrement déphasé) pointent TOUS vers le MÊME mécanisme racine :**
**OCaml traite chaque "item" (challenge, commitment, round bulletproof)
en UNE PASSE LOCALE complète (squeeze→convert→fold, ou check→fold) avant
de passer à l'item suivant, alors que notre port RUST BATCHE chaque PHASE
séparément à travers TOUS les items** (tous les squeezes d'abord, toutes
les conversions ensuite, tous les folds à la fin — ou l'inverse selon la
fonction). C'est exactement la structure de `ipa_challenges_transcript`
(bullet_reduce_challenges séparé de bullet_reduce_terms) MAIS le MÊME
schéma se retrouve ailleurs (oracles, combine_commitments) — **ce n'est
pas un bug localisé au bulletproof, c'est un pattern architectural
systémique dans TOUT `incrementally_verify_proof`.**

**Pourquoi l'essai `bullet_reduce_interleaved` (cette session, revert
final) n'a pas suffi malgré un mécanisme prouvé correct** : il ne
corrigeait qu'UNE instance de ce pattern (le bulletproof) sur plusieurs
qui existent dans la même fonction — d'où l'amélioration locale (543-700)
mais la régression ailleurs (4096-8192), puisque le reste de la fonction
(oracles, combine_commitments) reste batché et donc DÉSYNCHRONISÉ
différemment par rapport au nouveau layout amont.

**Ce qu'il faudrait pour vraiment fermer l'écart** : une réécriture
complète et HOLISTIQUE de `incrementally_verify_proof` (et possiblement
`combine_commitments`) en miroir strict et LIGNE-À-LIGNE de
`wrap_verifier.ml`, où CHAQUE item (challenge, commitment, round) est
squeeze→converti→plié avant de passer au suivant — PAS une série de
correctifs locaux. C'est un chantier de plusieurs heures, à haut risque
de régression si fait par morceaux (déjà démontré 2 fois cette session :
combine_commitments seul ne suffit pas, bulletproof seul ne suffit pas).
Prochaine session : soit s'attaquer à CETTE réécriture complète d'un
coup (avec mesure après CHAQUE sous-étape, jamais en fin de parcours),
soit accepter 2869 comme palier stable et documenté, et chercher un axe
totalement différent (ex. le row-40 encodage, cosmétique mais peut-être
plus vite gagnable pour réduire le compteur "divergent rows" même sans
toucher Generic).

## FIX RÉEL — combine_commitments réordonné (2026-07-13)

**Correction confirmée et committée** (`d479fdc58c`), basée sur une lecture
PRÉCISE d'OCaml (pas une déduction depuis les patterns de gates) :
`check_bulletproof` (`wrap_verifier.ml:580-606`) absorbe `cip` et calcule
`u = group_map(squeeze)` **AVANT** `Split_commitments.combine` (=
`combine_commitments`). Notre code appelait `combine_commitments` AVANT
ces deux étapes. Réordonné pour matcher exactement. **Résultat : 2869 →
2756 divergent rows**, step toujours FULL MATCH, 9/9 recorded.

**Correction de mon erreur précédente** : en relisant `bullet_reduce`
(`wrap_verifier.ml:168-184`) directement, j'ai confirmé qu'il N'EST PAS
interleaved — c'est exactement notre structure batch-puis-batch d'origine
(`Array.map` sur tous les gammas pour les prechallenges, PUIS `Array.map2`
séparé pour les termes/fold). Mon hypothèse d'interleaving de la session
précédente (`bullet_reduce_interleaved`) était donc FAUSSE depuis le
départ — heureusement reverté avant. **Ne plus retenter l'interleaving du
bulletproof.**

**Vérifié fidèles (pas de bug là) en relisant le source OCaml
directement** : `Common.ft_comm` (`common.ml:195-214`, notre
`commitments.rs::ft_comm` matche exactement l'ordre
`f_comm=scale(sigma,perm)` → `chunked_t` → `sum+negate(scale(chunked_t,
zeta_to_domain_size))`) ; `squeeze_scalar` (`constrain_low_bits:false`
des deux côtés) ; l'ordre `sponge_before_evaluations = clone AVANT
squeeze(digest)`.

**Piste explorée et RÉFUTÉE** : l'hypothèse que `bullet_reduce`
absorbe `(l,r)` en UN SEUL appel combiné (`absorb (PC::PC) gammas_i`)
alors que notre `bullet_reduce_challenges` fait deux `absorb_commitment`
séparés (l puis r) — semblait prometteuse mais **réfutée par lecture du
code** : `absorb_commitment` boucle déjà élément-par-élément
(`sponge.absorb(x); sponge.absorb(y)`), donc regrouper l et r dans un seul
appel produirait la MÊME séquence d'absorbs élémentaires qu'actuellement.
Ne pas retenter sans nouvelle preuve.

**Résiduel non résolu — micro-décalage périodique dans
`bullet_reduce_challenges`.** Après le fix combine_commitments, la région
~row 880-1220 (la boucle d'absorption/squeeze des ~15-16 rounds
bulletproof) montre un motif répétitif : chaque "round" (~13 rows) a une
interruption `Zero`/`Generic` (le pattern `lowest_128_bits`/troncature de
squeeze) à une position légèrement DIFFÉRENTE entre jsoo et rust (décalage
de 1-3 rows par round, cumulé sur 15-16 rounds ≈ explique une bonne partie
du déficit Generic résiduel, 555 vs 569 = -14, un chiffre qui correspond
bien à "quelques rows manquantes par round × 15-16 rounds"). Outil
utilisé pour cette localisation : **le label JSON intégré au dump rust
(`rust.labels[row]`, index-aligné, PAS le texte `SNARKY_LOG_CONSTRAINTS`
qui a un offset `log_row+40` qui n'est plus fiable après ce fix** (la
correspondance a changé puisque la structure a changé — à recalibrer si
réutilisé). Cause précise non identifiée — nécessiterait de comparer
coefficient-par-coefficient les rows de troncature 128-bit des deux côtés
dans CE round spécifique, avec le même niveau de rigueur (lecture directe
d'OCaml) que pour combine_commitments, plutôt que deviner depuis les
patterns.

## Nouvelle piste précise — x_hat / public_input_commitment (non résolue)

En cherchant la source du "résiduel" ci-dessus avec le label JSON
(`rust.labels[row]`), le vrai premier point de divergence de TYPE (rows
700-810, AVANT le bloc bulletproof, PAS après comme supposé) s'est révélé
être `scale_fast` (label direct), juste après un `split_field: odd bit` —
signature de `public_input.rs::public_input_commitment`'s traitement des
`Term::Packed` (x_hat / IVC Step 3), PAS le bulletproof. Jsoo fait autre
chose à cet endroit (pas de VarBaseMul visible dans cette fenêtre), donc
le x_hat lui-même est probablement mal positionné/ordonné en gates, pas
seulement le bulletproof plus loin.

**Différence structurelle repérée en comparant `public_input_commitment`
(public_input.rs:140-179) à `wrap_main.ml`'s x_hat (lignes 893-956)** :
OCaml partitionne les termes du public input en `constant_part` (valeurs
Field.Constant connues à la compilation — `lagrange`/`scaled_lagrange`
pré-calculés, AUCUN gate) et `non_constant_part` (`Cond_add`/
`Add_with_correction`, ce que nous traitons). L'accumulateur initial
OCaml (`init`) est `correction` (somme des corrections `Add_with_correction`)
PUIS on y ADDITIONNE les `constant_part` AVANT de plier les termes
non-constants. **Notre `public_input_commitment` (public_input.rs:147-156)
n'a pas de variante `Term::Constant` du tout** — si un slot du statement
wrap est un `FieldVar::Constant` (ex. `branch_data`, ou un flag figé),
OCaml le traite GRATUITEMENT (zéro gate, juste une addition de point
constant précalculé) alors que nous le forcerions probablement à passer
par le chemin `Packed`/`Cond` générique (coûteux, potentiellement avec un
ordre différent). **Pas encore vérifié si le statement wrap a RÉELLEMENT
des slots constants en pratique** (le step FULL MATCH suggère que non
pour le cas minimal, mais le WRAP a des slots différents — feature flags,
branch_data — à vérifier un par un contre `wrap_statement_terms`,
step_verifier.rs).

**Piste `constant_part` VÉRIFIÉE ET RÉFUTÉE** : le x_hat en row 700-810
concerne en fait le statement du **STEP** (pas le wrap) — c'est
`wrap_main.rs` construisant `step_statement_elements` (via
`XHatInput::Statement` dans `incrementally_verify_proof`, appelé pour
vérifier la preuve STEP depuis le circuit WRAP). Vérifié dans
`api.rs:781-800` (`WrapStepStatementSlot::{Field,Packed,Bool}` →
`StepStatementElement::{Split,Packed,Bool}`) : **CHAQUE élément passe par
`sys.compute(...)`**, qui produit TOUJOURS un `FieldVar::Var` witnessé,
JAMAIS un `FieldVar::Constant`. Donc `constant_part` est structurellement
TOUJOURS vide côté rust pour ce statement — la piste "gérer les
constantes" ne s'applique pas ici, confirmée par lecture directe du code
(pas juste supposée). **Ne pas retenter cette piste sans nouvelle preuve.**

**Où chercher ensuite (non fait)** : puisque ce n'est pas le
constant/non-constant split, la divergence row 700-810 doit venir soit
de l'ORDRE exact des termes dans `step_statement_elements` (le layout
`WrapStepStatementSlot` construit dans `recorded.rs`/ailleurs — à
comparer avec l'ordre exact de `Wrap.Statement.to_data`/spec OCaml pour
le STEP statement, PAS le wrap statement, cette fois), soit d'un détail
de `scale_fast2_prime`/`lagrange_with_correction` (le calcul de la
correction Lagrange elle-même) qui diffère de
`Ops.scale_fast2'`/`lagrange_with_correction` OCaml (lignes 382-430+ de
wrap_verifier.ml, pas encore lues en détail cette session).

**Suite (même session) — chaîne COMPLÈTE de vérifications, TOUTES
fidèles, aucun bug trouvé** :
- `lagrange_with_correction` (wrap_verifier.ml:382-443) : intégralement
  CONSTANT (branche `which_branch=1` → `base_and_correction` direct,
  zéro gate) — ne peut pas être la source d'un écart de gates.
- `Ops.scale_fast2'`/`scale_fast2` (plonk_curve_ops.ml:236-278) : witness
  `(s_div_2,s_odd)` via `exists` + `Assert.equal(2·s_div_2+s_odd, s)` +
  `scale_fast2` (unpack + contrainte top-bits=0 + select) — notre
  `scale_fast2_prime`/`scale_fast2` (plonk_curve_ops.rs:379-401,508-517)
  matche exactement, structure et ordre identiques.
- `wrap_main.ml::split_field` (ligne 57-69, DIFFÉRENT de
  `plonk_curve_ops.ml`'s propre split interne à scale_fast2') : witness
  `(y,is_odd)` + `Assert.equal(2y+is_odd,x)` — notre `split_field`
  (plonk_curve_ops.rs:417-448) matche. Le "double split" (une fois dans
  `StatementElement::Split`, une deuxième fois DANS `scale_fast2_prime`
  appelé sur le résultat) est CONFIRMÉ voulu — OCaml fait exactement la
  même chose (`wrap_main.ml:491` `split_field x` produit un terme
  `Field(y,255)` qui repasse ENSUITE par `Add_with_correction`→
  `scale_fast2'`, qui re-split `y` en interne). Pas un bug.
- **`Spec.pack`'s traitement de `Digest`** (`spec.ml:229-230`) :
  `Digest -> \`Packed_bits (x, Field.size_in_bits)` — PAS
  `\`Field (Shifted_value ...)`. Donc le digest
  `messages_for_next_step_proof` (le SEUL élément du step statement pour
  N0, `unfinalized_proofs` étant un vecteur de longueur 0) ne passe
  JAMAIS par `split_field` dans `pack_statement`
  (`wrap_main.ml:487-493`, le filtre `\`Field (Shifted_value x) ->
  \`Field (split_field x)` ne s'applique qu'aux `\`Field`, pas aux
  `\`Packed_bits`). **Notre choix de `WrapStepStatementSlot::Packed{value,
  num_bits:255}` (api.rs:1478-1481, PAS `::Field`) est donc CORRECT** —
  j'ai failli le "corriger" à tort vers `::Field`, ce qui aurait
  introduit une régression. Vérifié avant de toucher au code, rien
  changé.

**Bilan** : toute la chaîne de fonctions impliquées dans le x_hat/step
statement (ft_comm, absorb_shifted, squeeze_scalar/lowest_128_bits,
lagrange_with_correction, scale_fast2/scale_fast2'/split_field, le type
de packing du Digest) est vérifiée fidèle à OCaml, ligne par ligne. La
divergence résiduelle des rows 700-810 (et le reste, 1024+) doit donc
venir d'ailleurs — soit une différence subtile dans les VALEURS
witnessed elles-mêmes (peu probable, les tests recorded passent), soit
un endroit non encore identifié. **Prochaine piste à explorer (non
commencée)** : comparer précisément `messages_for_next_step_proof`'s
propre calcul (`Wrap_hack.Checked.hash_messages_for_next_wrap_proof` /
`hash_messages_for_next_step_proof` côté step) — c'est la fonction qui
PRODUIT le digest witnessed, en amont de tout ce qui a été vérifié ici;
si SA construction (ordre des inputs Poseidon) diffère, ça expliquerait
un décalage qui se propage ensuite sans qu'aucune des fonctions
vérifiées ci-dessus soit en cause.

## 3 essais de réordonnancement du witnessing api.rs — TOUS reverted

Suite à la découverte que `wrap_main.ml` witnesse `openings_proof` (lr,
z1, z2, delta, sg) AVANT `messages` (w_comm, z_comm, t_comm)
(wrap_main.ml:440-477 : `let openings_proof = exists (...)` précède
`let messages = exists (...)`), 3 variantes testées sur la base du fix
combine_commitments (2756, confirmé) :

1. **`openings` avant `messages`, `vk_digest` déplacé après les deux**
   (matching littéral de l'ordre OCaml complet) → **3090** (pire).
2. **Seulement `vk_digest` déplacé après messages+openings** (sans
   toucher l'ordre messages/openings) → **3090** (identique à #1 —
   montre que déplacer `vk_digest` tard est LE facteur dominant de la
   régression).
3. **Seulement `openings` avant `messages`** (en gardant `vk_digest` à
   sa position actuelle, entre messages+h et openings) → **3090**
   (identique aussi — montre qu'INVERSER messages/openings est LUI AUSSI
   à lui seul suffisant pour régresser, indépendamment de vk_digest).

**Conclusion** : les deux changements (position de vk_digest ET ordre
messages/openings) sont CHACUN individuellement nuisibles au score
actuel, malgré le fait que l'ordre OCaml LITTÉRAL est
`openings→messages→[digest calculé plus tard, dans incrementally_verify_proof]`.
Ceci confirme (pour la 3e fois cette session, cf. essais précédents
`6abbec7b88`/`91bf44b457`) que l'optimum EMPIRIQUE actuel (`messages`
avant `openings`, `vk_digest` calculé tôt) est un minimum local
robuste — le vrai ordre OCaml ne peut être atteint que par un
changement plus large et cohérent (probablement en même temps que le
sous-ordre exact à l'intérieur de `messages`/`openings` eux-mêmes, pas
juste leur ordre relatif). **Ne plus retenter ces 3 variantes
individuellement** — si retenté, le faire en changeant PLUSIEURS choses
à la fois (ex. l'ordre relatif ET le sous-détail du digest EN MÊME
TEMPS que le fix scale_fast/split_field interne), pas un seul facteur
isolé comme ici.

Toutes les 3 variantes ont été testées avec build+9/9 recorded+mesure
gate-diff complète avant d'être revertées ; le repo est resté systématiquement
propre entre chaque essai. État final : 2756 divergent rows, 555/569
Generic, step FULL MATCH, 9/9 recorded — confirmé stable.

## Essai `h` constant — testé, REVERT (contre-intuitif)

Vérifié dans `wrap_verifier.ml:618` et `:965` : `Generators.h` (le point
de blinding SRS) est TOUJOURS `Inner_curve.constant (Lazy.force
Generators.h)` côté OCaml — jamais witnessé, jamais checké on-curve.
Notre code faisait `let h = mkpt(sys, w.h)?` (witness + check on-curve,
3 gates). Changé en `let h = cpt(w.h)` (constant, zéro gate) — **9/9
recorded toujours OK** (donc mathématiquement h a bien la même valeur,
aucun problème de correction), **mais divergence 2756 → 3507** (bien
pire), Generic 555→554. Reverté. La lecture OCaml était juste, mais le
retrait du check on-curve de `h` désaligne visiblement le pairing
double-generic en aval de façon plus large que le gain local — même
mécanisme de cascade déjà vu plusieurs fois cette session (un changement
individuellement fidèle à OCaml peut régresser le score global si le
reste du circuit n'est pas ajusté en même temps). **Ne pas retenter
isolément** — si retenté, le faire en même temps qu'un ajustement du
pairing dans la région immédiatement après (rows ~620-660).

**Bilan de cette dernière série d'essais (4 au total ce tour)** : TOUS
individuellement fidèles à une lecture précise d'OCaml, TOUS testés avec
build+9/9 recorded+mesure complète, TOUS régressent (3090, 3090, 3090,
3507) par rapport au 2756 actuel. Ceci renforce fortement la conclusion
déjà documentée : le circuit rust est actuellement dans un minimum local
robuste où des corrections PARTIELLES (même correctes individuellement)
ne suffisent pas — il faut soit LE ticket complet (plusieurs changements
fidèles appliqués ENSEMBLE), soit accepter cet état comme palier stable.

**Essai combiné (h-constant + openings-avant-messages + vk_digest tard,
les 3 en même temps) — AUSSI reverté.** Résultat : 3507 (identique au
h-constant seul). Ceci réfute l'hypothèse "il faut les combiner" pour
CETTE combinaison précise — combiner ne suffit pas non plus ici. La
piste "réécriture complète tout-en-un" reste la seule non encore
essayée sérieusement ; les combinaisons partielles ad hoc ont maintenant
toutes échoué (5 essais distincts cette session : lr-interleaved seul,
openings-avant-messages seul, vk_digest-tard seul, h-constant seul, et
la combinaison des 3 derniers).

## BRANCHE `wrap-iso-rewrite` — réécriture iso-OCaml du wrap (2026-07-12+)

**Décision utilisateur** : nouvelle branche dédiée à rendre le corps du
circuit wrap STRUCTURELLEMENT IDENTIQUE à `wrap_main.ml`/`wrap_verifier.ml`,
**sans se soucier des régressions de gate-parity pendant la transition**.
Critères : ça compile, `--lib` (101) et `recorded` (9/9, N0/N1/N2) passent
à chaque commit. La mesure/optimisation de la sortie (`rust-pickles-wrap-
gates-diff.ts`) ne reprendra QUE lorsque le code sera devenu le miroir
d'OCaml — à ce moment-là seulement on comparera et corrigera la sortie.

### Fait sur cette branche (chaque étape = 1 commit, tests verts)

1. `d5b43a0bd6` (utilisateur) — witness schedule : sg_olds → openings
   (lr/z1/z2/delta/sg) → messages → digest (déplacé après les witnesses).
2. `029dd5bc8c` — **digest d'index calculé DANS `incrementally_verify_proof`**
   (enum `IndexDigest { ComputeFromVk, SpongeAfterIndex, Precomputed }`,
   miroir de wrap_verifier.ml:850-866 / step_verifier.ml:533-537). Le
   paramètre `vk_digest` de `wrap_main` est SUPPRIMÉ ; le chemin step garde
   transitoirement `Precomputed` (à migrer vers `SpongeAfterIndex`). Le
   test lib `wrap_main_assembles_with_satisfying_ipa` recalcule le digest
   depuis les 28 points (mirror out-of-circuit) au lieu d'un random.
3. `7961133e6e` — réordonnancement du corps api.rs vers l'ordre wrap_main.ml :
   éléments du prev_statement witnessés après branch_data (:191),
   `expand_feature_flags`+`assert_consistent` déplacés APRÈS `choose_key`
   (:249-299), boucle unfinalized (old_bp_chals/evals) après `prev_step_accs`
   (:306-421), `h = Generators.h` en CONSTANTE de circuit (plus witnessé
   ni checké on-curve, wrap_verifier.ml:618/:965).
4. `e1812a075f` — **`openings_proof`/`messages` witnessés DANS `wrap_main`**
   via une closure `witness_proof: FnOnce(&mut RunState<F>) ->
   (OpeningProof, Messages)`, appelée après le bloc finalize/hash-prev —
   position d'émission exacte de wrap_main.ml:440-477. L'ordre de
   contraintes DANS le exists (on-curve lr, forbidden z1, forbidden z2,
   on-curve delta, on-curve sg ; puis w_comm/z_comm/t_comm) matche déjà
   l'ordre des checks du typ OCaml.
5. `9b7ccfcb36` — `actual_proofs_verified_mask` (`Util.ones_vector` sur
   `Pseudo.choose`) émis à la position :165 (juste après which_branch,
   avant domain_log2) dans api.rs et passé en paramètre ; boucle
   finalize+hash-prev SCINDÉE en deux passes (:361-421 puis :423-427,
   identique en N0/N1, différent en N2).

### Restant pour l'iso complet (ordre de priorité)

1. **OptSponge comme sponge principal du wrap — FAIT** : enum
   `Transcript { Plain, Opt }` dans incrementally_verify.rs, paramètre
   `use_opt_sponge` (wrap = true via wrap_main, step = false via
   verify_one), absorbs via `Opt.absorb (Boolean.true_, x)`, beta/gamma =
   `Opt.challenge` (lowest_128 constrain=true), alpha/zeta =
   `Opt.scalar_challenge` (constrain=false), et conversion opt→plain à
   IVC Step 13 via `OptSponge::into_squeezed_parts()` +
   `DuplexState::from_var_state_squeezed()` (nouveau constructeur snarky,
   miroir de `S.make ~state ~sponge_state:(Squeezed n)`,
   wrap_verifier.ml:1294-1304). Validé : 101/101 lib + 9/9 recorded (le
   transcript OptSponge à flags constants true produit les MÊMES valeurs
   que le sponge simple — soundness intacte, prouvé de bout en bout par
   les recorded).
2. Digest d'index du step calculé in-circuit — **FAIT** (via
   `IndexDigest::ComputeFromVk` sur le chemin step aussi) : `verify_one`
   ne prend plus de `vk_digest` witnessé ; le digest est dérivé
   in-circuit des 28 points du VK VÉRIFIÉ (`p.vk`), ce qui est le même
   calcul que le copy+squeeze OCaml de step_verifier.ml:533-537 (les
   deux = sponge frais sur les 56 coordonnées du VK vérifié). Champ
   `wrap_vk_digest`/`vk_digest` supprimé de `RecursiveStepData`,
   `PerProofInput` et du test lib (dont le mirror recalcule le digest
   depuis `ivp_vk` en ordre ComputeFromVk). Validé stable_n1_chain
   inclus (9/9). NOTE : la variante `SpongeAfterIndex` (partage du
   sponge entre le hash d'accumulateur et le digest, comme OCaml qui
   n'absorbe le VK qu'UNE fois) reste NON utilisée — elle exigerait que
   `PerProofInput.sponge_after_index` porte sur le VK vérifié, or notre
   chaîne stable le construit sur le VK haché dans le statement
   PRÉCÉDENT (recursive_step.rs `wrap_vk_pts =
   previous_messages_vk_pts`), qui diffère au premier step stable. En
   OCaml les deux coïncident par construction (le
   messages_for_next_step_proof d'un proof contient le dlog_plonk_index
   de son PROPRE système). Tant que notre modèle de données garde cette
   distinction, ComputeFromVk (2 passes d'absorption au lieu d'1) est
   la forme iso-correcte atteignable ; le partage exact du sponge est
   une optimisation/fidélité de plus qui demanderait d'aligner
   `wrap_vk_pts` sur le VK vérifié.
3. Granularité fine des `exists` du prev_statement — **FAIT** : la boucle
   fusionnée d'api.rs est scindée en 4 phases aux positions OCaml exactes :
   (a) valeurs déférées des unfinalized (struct local `UnfDeferred` :
   alpha/beta/gamma/zeta/xi/cip/b/perm, bulletproof_challenges, sponge
   digest, should_finalize) witnessées à :191 AVANT `choose_key`, juste
   avant les éléments du prev_statement ; (b) `prev_step_accs` per-proof
   (`unf_prev_step_accs`) à :301, juste après les sg_olds physiques ;
   (c) `old_bp_chals` (les deux copies : finalize + hash d'accumulateur) à
   :306 ; (d) `evals`/ft_eval1/public_evals à :341-349, le finalize
   restant dans `wrap_main` (:409-419). Identique en N0 (0 unfinalized),
   affecte l'ordre d'émission en N1/N2. Validé 101/101 + 9/9 recorded.
   RESTE un détail d'ordre INTERNE aux evals non traité : OCaml
   `All_evals` witnesse public_input d'abord, puis les colonnes dans
   l'ordre du typ `Evals` (w[15], coefficients[15], z, s[6], puis les 6
   sélecteurs), ft_eval1 en dernier ; notre `AbsorbEvalsVar` lit
   evals_flat dans l'ordre z, sélecteurs, w, coefficients, s, puis
   ft_eval1 et public_evals — réordonner exige de changer AUSSI le
   packing out-of-circuit d'`evals_flat` (recorded data pairing
   positionnel), à faire en une passe dédiée.
4. Le masque dynamique dans `verify` — **FAIT**, et la fausse piste
   historique est RÉSOLUE : le blocage était bien l'absence du port
   `Opt` dans la combinaison. `Split_commitments.combine`
   (wrap_verifier.ml:496-566 sur pcs_batch.ml:18-40) est maintenant
   porté fidèlement dans `bulletproof.rs::combine_commitments` :
   entrées `CommitmentOpt { Just, Maybe(keep, p), Nothing }`, liste
   traitée en INVERSE (init = dernière entrée non-Nothing), chaque
   `scale_and_add` = `if acc.non_zero then p + endo(acc, xi) else p`
   puis `if keep then ... else acc.point`, suivi de
   `non_zero = keep ||| acc.non_zero`, et `Boolean.Assert.is_true
   non_zero` final. Les sg_old entrent en `Maybe(keep, sg)` avec le
   masque DYNAMIQUE (`actual_proofs_verified_mask`, inversé pour
   s'aligner sur le padding physique dummies-devant, sémantique
   `extend_front`), le reste en `Just`. Le hack "skip si masque
   constant-zéro" est SUPPRIMÉ. Côté step, le masque constant-true se
   replie par constant-folding (`sys.if_` court-circuite les conditions
   constantes) — comportement inchangé. Validé 101/101 + 9/9 recorded
   (y compris N1/N2 où le masque dynamique est réellement variable).
5. **Ordre interne des `evals` — FAIT** : OCaml
   `All_evals` witnesse `public_input` (les évaluations x_hat) D'ABORD,
   puis les colonnes dans l'ordre du typ `Evals` (w[15],
   coefficients[15], z, s[6], generic_selector, poseidon_selector,
   complete_add_selector, mul_selector, emul_selector,
   endomul_scalar_selector), et `ft_eval1` EN DERNIER (ordre hlist de
   `{ evals = { public_input; evals }; ft_eval1 }`). Notre
   `AbsorbEvalsVar`/`FinalizeEvals` lisait auparavant `evals_flat` dans
   l'ordre z, sélecteurs(6), w(15), coefficients(15), s(6), puis ft_eval1
   et public_evals. Les deux flatteners (`Fp` et `Fq`) produisent maintenant
   `w → coefficients → z → s → sélecteurs`; les quatre lecteurs in-circuit
   (`api.rs`, les deux chemins `recursive_step.rs`, et les fixtures lib)
   témoignent `public_input` d'abord, consomment ce nouvel ordre, puis
   témoignent `ft_eval1` en dernier. L'appariement positionnel est donc
   modifié atomiquement des deux côtés. Validé : cargo check, 101/101 lib
   et 9/9 recorded (N0/N1/N2, stable N1 inclus).
   Le code est maintenant structurellement aligné sur les écarts identifiés ;
   prochaine étape : reprendre la mesure `rust-pickles-wrap-gates-diff.ts`
   après rebuild napi et re-trier les divergences résiduelles.
6. **Partage du sponge d'index côté step — FAIT** : `verify_one` utilise
   désormais `IndexDigest::SpongeAfterIndex` dès que le statement précédent
   et la VK du wrap vérifié coïncident. `RecursiveStepData` porte un booléen
   de migration `share_index_sponge` : le premier passage après un changement
   de circuit conserve `ComputeFromVk` pour pouvoir vérifier l'ancien
   statement, puis tous les cycles stabilisés copient/squeezent le sponge
   déjà initialisé avec les 28 engagements de la VK vérifiée — une seule
   absorption du VK, comme `step_verifier.ml:533-537`.
   `prove_next_recursive_cycle_with_real_vk` est maintenant réellement en
   deux passes : bootstrap du prochain wrap, extraction de sa VK, puis
   reconstruction du step+wrap final avec cette VK ; stabilité de l'index
   assertée. La fixture `step_main` impose également que le sponge du message
   et la VK vérifiée soient la même liste canonique.
   Validé : cargo check, 101/101 lib, 9/9 recorded (stable N1 inclus) et
   `rust-pickles-step-gates-diff.ts` **STEP GATES: FULL MATCH** (512/512,
   histogrammes et rows exacts).

### Méthode de validation pendant la réécriture

À chaque commit : `cargo build -p pickles --release` +
`cargo test -p pickles --release --lib` (101) +
`cargo test -p pickles --release --test recorded` (9/9). PAS de mesure de
gate-diff pendant cette phase (choix explicite utilisateur).

### Première cible du diff wrap : typ des ouvertures — FAIT

L'instrumentation OCaml tranche l'ambiguïté sur les points témoignés avant
le digest de VK. Entre l'entrée de `wrap_main` et la première Poseidon,
`exists Bulletproof.wrap_typ` (ligne 440) n'émet aucune contrainte de courbe,
alors que `Messages.wrap_typ` (ligne 471) émet exactement 46 `Square` et 23
`R1CS`, soit le check des 23 points de messages. Rust utilisait `mkpt`, donc
`assert_on_curve`, pour les 30 points LR, `delta` et `sg` des ouvertures : 32
points et 64 rows Generic superflues. Un constructeur `mkpt_opening` séparé
témoigne uniquement ces points sans check ; les messages et tous les autres
points restent sur le typ vérifié.

Validation complète : `cargo check`, 101/101 tests lib, 9/9 tests recorded,
et step toujours **FULL MATCH** (512/512). Après rebuild NAPI, le wrap passe
de Generic 682 à 614, la première Poseidon de la row 310 à 242 (OCaml : 231),
et le total de rows divergentes de 4199 à 4080. Les quatre Generic retirées
en plus des 64 checks viennent du repacking des contraintes. La prochaine
cible localisée est donc le reliquat exact de 11 rows avant la première
Poseidon, puis le train OptSponge (+22 Poseidon Rust).

### Deuxième cible : préambule du transcript wrap — FAIT

La capture HL croisée a isolé deux différences après les `sg_old`. Rust
appelait `check_other_field_packed` sur les représentants `z1` et `z2` de
l'ouverture ; OCaml passe directement de `exists Bulletproof.wrap_typ` aux
69 contraintes on-curve de `Messages.wrap_typ`. Ces deux blocs forbidden
(2 × 6 contraintes HL) ont donc été supprimés, comme les checks de points
d'ouverture du jalon précédent.

Le bloc de cohérence des features différait aussi : OCaml émet 10 R1CS + 2
Equal, Rust 8 R1CS + 14 Equal au niveau HL, mais les Equal identitaires sont
compactées en deux rows par le backend. Les assertions `assert_consistent`
sont conservées et les deux résultats de `Boolean.any` (`table_width_at_least_1`
et `lookups_per_row_4`) reçoivent désormais le check booléen qu'émet OCaml.

Résultat après rebuild NAPI : première Poseidon **row 231 des deux côtés** ;
aucune divergence de type avant row 699. Le diff total passe de 4080 à
**3173**, avec Rust Generic 603 contre OCaml 569 (anciennement 614/569).
Validation : 101/101 lib, 9/9 recorded et step **FULL MATCH**. La prochaine
cible structurelle est la rupture du train OptSponge à partir de row 699.

### Troisième cible : rupture row 699 — correction et essais réfutés

Instrumentation conservée : `SNARKY_LOG_PENDING_GENERIC=1` journalise la
création, la fusion et le flush de chaque demi-gate Generic avec `next_row`,
label et localisation. Elle est inactive par défaut. Des localisations de
site distinctes sont également conservées dans `ft_comm`, les additions de
l'équation bulletproof, `combine_commitments` et l'addition conditionnelle
du public input, afin que les futures traces ne reposent plus sur le seul
label global `wrap_main: verify step proof`.

Essais effectués avant le diagnostic final (tous revertés lorsqu'ils étaient
sans effet ou régressifs) :

1. suppression conditionnelle de l'assertion finale `non_zero` de
   `combine_commitments` lorsqu'un `CommitmentOpt::Just` existe : aucun gate
   modifié ; l'assertion était déjà réduite ;
2. unification directe du dernier `n_acc` de `scale_fast_unpack` avec le
   scalaire dans la dernière row `VarBaseMul` : aucun gate modifié ;
3. alimentation de `cached_constants` depuis les branches R1CS qui imposent
   `Var × Constant = Constant` : aucun gate modifié ;
4. publication différée dans `cached_constants` pendant les custom gates :
   17/17 tests Snarky verts, mais gate diff strictement inchangé ;
5. matérialisation explicite des coordonnées constantes avant/après
   `CompleteAdd`, testée globalement puis localement sur `ft_comm` et
   `combine_commitments` : la variante globale alignait 699 mais inversait
   595/596 ; les variantes locales candidates étaient des no-op ;
6. replay différé des Generic autour du doublement initial de `scale_fast` :
   régression 3173 → 3175 avec nouvelles divergences 595/596 ;
7. variant `EcAddCompleteDeferred` porté dans `KimchiConstraint` puis utilisé
   dans `combine_commitments` : aucun effet, ce qui a prouvé que l'attribution
   du site était fausse ;
8. suspension du flush autour de l'addition conditionnelle directement dans
   `public_input_commitment` : aucun effet, car l'addition réelle est interne
   à `scale_fast2`.

Diagnostic définitif via la trace : la row interne 659 (wrap 699) est la
matérialisation Generic de `h_minus_g = h + (-g)` dans `scale_fast2`, juste
après les 51 rows `VarBaseMul` et juste avant `Point::select`. Le correctif
conservé suspend `flush_generic_before_custom` uniquement pendant cet
`add_fast`, puis restaure la politique avant les `if_`. Résultat : les
divergences de type rows **699–700 disparaissent**, le total passe de 3173 à
**3171**, sans nouvelle divergence plus tôt ; la première divergence de type
est désormais row **704**. Histogramme inchangé (Rust Generic 603, Poseidon
1023, CompleteAdd 264, EndoMul 2528 ; OCaml 569/1001/258/2464), ce correctif
aligne l'ordre plutôt que le nombre de gates.

Validation : test ciblé `scale_fast2_prime`, 101/101 lib, 9/9 recorded et
step **FULL MATCH**. Prochaine cible : utiliser les labels et
`SNARKY_LOG_PENDING_GENERIC` conservés pour attribuer les divergences
704–711, puis le premier train OptSponge 711+.

### Quatrième cible : ordonnancement x_hat rows 704–710

Les labels de site ajoutés à `public_input_commitment` et la trace
`SNARKY_LOG_PENDING_GENERIC=1` attribuent précisément les deux ruptures :
la row interne 664 est la dernière réduction de `public_input packed add`,
et la row interne 667 celle de `public_input blinding add`. Avec la politique
globale `flush_generic_before_custom`, Rust les émettait avant leur
`CompleteAdd`, tandis qu'OCaml place le custom gate avant la demi-row Generic.

Deux variantes incorrectes ont été mesurées puis revertées :

1. suspendre le préflush autour des deux additions sans flusher ensuite
   laisse la contrainte `packed` ouverte et la mélange aux gadgets suivants ;
   le diff régresse de 3171 à 3468 ;
2. ne suspendre que l'addition `packed`, toujours sans flush explicite,
   produit la même cascade (3468), ce qui réfute l'hypothèse d'une simple
   inversion locale sans frontière de flush.

Le correctif conservé expose `flush_pending_generic()` dans le constraint
system et applique la séquence exacte au fold x_hat : désactiver le préflush,
émettre `CompleteAdd`, restaurer la politique, puis flusher immédiatement
pour l'addition `packed`. Pour le blinding, la demi-row reste ouverte afin
d'être fusionnée au premier `opt_sponge add_in`, conformément à la trace.
Les divergences de type **704–705 et 707–708 sont supprimées**, sans nouvelle
divergence antérieure ; le diff total passe de **3171 à 3170**. Les labels et
l'instrumentation restent présents, inactifs sans variable d'environnement.

La première divergence de type est maintenant la row **711** : OCaml démarre
le premier Poseidon, Rust y flush encore une demi-row `opt_sponge add_in`.
La trace Rust autour de la frontière est : packed pending row 664, custom
row 664, flush row 665 ; blinding pending row 667, custom row 667 ; fusion
avec opt_sponge rows 668–670, puis pending/flush row 671 (wrap row 711).
Les coefficients montrent également que la première demi-contrainte Rust
après le blinding vient de la réduction du `CompleteAdd`, alors que les trois
rows OCaml 708–710 contiennent exactement six slots. La prochaine correction
doit donc aligner la réduction du blinding/accumulateur (ou le nombre exact
d'absorptions OptSponge), et non ajouter un nouveau réglage de flush aveugle.

Validation de ce jalon : 101/101 tests lib, 9/9 recorded, step **FULL MATCH**,
wrap 8192/8192 rows et première divergence de type repoussée à 711.

### Cinquième cible : custom gates exacts et Generic résiduel +10

Les commits Claude suivant le jalon x_hat ont changé le diagnostic de façon
importante (ils n'avaient pas encore été reportés dans ce fichier) :

1. `638dd90463` aligne `reduce_lincom`/`canonicalize` sur le `Map.fold_right`
   OCaml en triant les variables par index croissant plutôt que par valeur de
   coefficient. Cela corrige les slots l/r inversés des contraintes à deux
   termes, notamment dans `opt_sponge add_in` ;
2. `59f0299ec7` corrige le cas de base : avec
   `Max_proofs_verified = 0`, la preuve step ne transporte AUCUN challenge de
   récursion kimchi. Le vecteur `sg_old` in-circuit est donc vide, sans absorbs
   de zéros masqués ni entrées `Maybe` dans `combine_commitments`. Tous les
   types de custom gates deviennent exacts : Poseidon 1001, EndoMul 2464,
   CompleteAdd 258, VarBaseMul 663 et EndoMulScalar 184 ;
3. `9d4930b21c` documente le recensement des marqueurs on-curve jsoo : delta
   et sg avant le sponge, puis un point lr par round bulletproof ;
4. `d91443851d` porte ce recensement : les openings lr/delta/sg passent par
   `Inner_curve.typ`, les points VK sélectionnés restent unchecked (aucun
   marqueur VK côté jsoo), et `endo_inv` vérifie son point témoigné. Il retire
   également le préflush global des demi-rows Generic avant custom gates : le
   backend OCaml les conserve à travers les custom rows jusqu'à la prochaine
   moitié. Les marqueurs sont **73 = 73**, tous les custom gates restent
   exacts, et le résiduel devient Rust Generic **579** contre OCaml **569**.

Validation déclarée et reproduite au dernier commit : step **FULL MATCH**,
101/101 lib et 9/9 recorded. Le travail restant porte maintenant sur dix rows
Generic et leurs coefficients/wiring, plus les divergences de permutation ;
il ne faut plus chercher une différence de structure Poseidon/EC/endo.

Essais postérieurs au commit `d91443851d`, mesurés puis revertés :

- ajouter les deux checks `Other_field.Packed.typ` des valeurs interdites de
  z1/z2 dans `api.rs` fait passer Generic **579 → 592** (+13) et décale le
  circuit dès la première région custom. Cette tentative non commitée a été
  retirée ; ces checks ne sont pas absents à cet endroit sous cette forme ;
- supprimer `opt_sponge::add_in` lorsque `x` est la constante zéro fait passer
  Generic **579 → 544** (-35) et crée 3961 divergences, dès row 231. OCaml
  conserve donc ces contraintes (ou leurs alias matérialisés) ; ne pas ajouter
  cette optimisation globale.

Prochaine méthode : repartir strictement de `d91443851d`, produire le diff
avec labels/HL logs, puis attribuer les dix Generic excédentaires par site.
Les custom histograms exacts servent désormais d'invariant : toute tentative
qui modifie un de leurs compteurs ou déplace le premier train Poseidon est une
régression à reverter immédiatement.

Mesure complémentaire sur ce baseline propre : les **73 marqueurs c=5 sont
exacts en nombre mais pas en position**. Jsoo les place aux rows 104–166 (32),
181–229 (25), puis 4261+74k (16). Rust les place aux rows 125–237 (57
contigus), puis 4271, 4345, et ensuite avec une période 75 jusqu'à 5395. Avant
le premier Poseidon, Rust compte donc 7 Generic de trop et démarre row 238,
contre row 231 côté jsoo. La décomposition est précise : Rust possède 21 rows
de plus avant le premier groupe openings, mais ne possède pas le gap jsoo de
14 rows entre les groupes de 32 et 25 marqueurs ; bilan net +7.

Le gap jsoo correspond à l'emplacement de z1/z2 dans `Bulletproof.wrap_typ`,
mais l'essai qui ajoutait seulement les forbidden checks (+13 rows) est
insuffisant et régressif puisqu'il ne retire pas simultanément les 21 rows
excédentaires antérieures. La prochaine passe doit donc comparer le bloc
pré-openings (prev_statement / feature expansion / choose_key) et déplacer le
traitement z1/z2 en une seule correction structurée. Ne pas réintroduire les
checks z1/z2 isolément.

### Sixième cible : pré-openings aligné, résiduel Generic +2

La comparaison des coefficients a attribué exactement les 21 rows en trop
avant les openings. Les 28 rows `choose_key` jsoo sont 75–102, mais Rust les
plaçait 80–107 : cinq rows provenaient de checks booléens explicites sur les
8 slots feature et le flag joint-combiner. Après `choose_key`, Rust émettait
encore seize rows de `expand_feature_flags/assert_consistent`, tandis que
jsoo passait directement au premier opening. Cause : ces slots publics ne
sont pas les `plonk.feature_flags` consommés par `wrap_main`; pour la branche
N0, les flags de la clé sélectionnée sont statiquement `Features.none` et le
bloc OCaml se replie à la compilation.

Correctif : suppression de ces 21 rows erronées, puis port des checks
`Other_field.Packed.typ` de z1/z2 au BON emplacement — après le witness des
32 points lr et avant delta/sg. Contrairement à l'essai isolé antérieur, les
deux changements forment une seule correction structurelle. Les positions
des 57 marqueurs pré-sponge sont désormais EXACTES : 104–166 (32), puis
181–229 (25) des deux côtés. Les 16 marqueurs bulletproof tardifs restent
présents, et tous les histogrammes custom restent exacts.

Résultat : Rust Generic **579 → 571**, OCaml 569 ; diff total **3171 →
2702**. Il ne reste que +2 Generic nettes. Avant le premier Poseidon, Rust a
au contraire une row de moins : jsoo row 230 contient deux demi-contraintes
(`1,0,0,0,0` et un R1CS `0,0,-1,1,0`), alors que Rust conserve seulement la
première en pending et démarre Poseidon row 230 au lieu de 231. Les trois
rows de différence nettes sont donc réparties : une demi/frontière absente
ici, puis trois rows excédentaires plus tard (les premiers sites visibles par
intervalles custom sont x_hat/OptSponge autour de 698–710, 1008–1084 et
1226).

Validation : 101/101 lib, 9/9 recorded, step **FULL MATCH**, wrap 8192/8192.

## Session nuit 2026-07-13 — deux fixes majeurs commis, état & pistes

### Fix 1 (snarky, commit `reduce_lincom`) : ordre des termes par INDEX
`reduce_lincom`/`canonicalize` triaient les termes par (coefficient, index)
(`terms_list.sort()` sur des tuples `(coeff, idx)`) — OCaml ordonne par
INDEX DE VARIABLE ASCENDANT uniquement (`Map.fold_right` sur la map indexée).
Résultat : slots l/r échangés dans les réductions 2-termes dès que l'ordre
des coefficients diffère de celui des index (observé dans les réductions
add_in du train opt-sponge, rows 701-702 — réparées par le fix). Step
FULL MATCH préservé, coeffs 610→573.

### Fix 2 (MAJEUR, api.rs) : base case sans recursion challenges kimchi
Preuve empirique par comptage des blocs endo (44 consécutifs jsoo vs 46
rust dans le combine) : **jsoo base case = `Max_proofs_verified 0` →
vecteur sg_old VIDE en circuit** (aucun absorb masqué-zéro, aucune entrée
Maybe dans le combine). Notre pipeline créait le step proof de base avec
2 `RecursionChallenge` dummy kimchi (`prove_with_recursion_mask(...,
vec![dummy; 2], Some(&[false,false]))`) et absorbait 4 zéros masqués
partout (oracles/wrap_witness/circuit — cohérent en interne mais PAS iso).
Fix : `vec![], Some(&[])` partout, `physical_sg_olds` sans resize dummy.
**Résultat : TOUS les gate types custom EXACTS** (Poseidon 1001, EndoMul
2464, CompleteAdd 258, VarBaseMul 663, EndoMulScalar 184). Reste Generic
585 vs 569 (+16). 9/9 recorded (N1/N2 inchangés : leur chemin sg_olds
non-vide ne passait pas par le resize).

### État de la mesure après les 2 fixes
- divergent rows 3293 (le total a monté vs 3170 mais c'est du
  RÉALIGNEMENT : les types customs sont désormais exacts, le pattern de
  divergence est un simple DÉCALAGE de ±4 rows entre les blocs).
- Première divergence de type : row 227. **Cause identifiée, non
  corrigée** : jsoo a 4 rows Generic (8 demi-gates, coefficient `05` =
  b de la courbe → ~2 points on-curve-checkés + 1 paire) juste AVANT son
  index sponge (jsoo sponge à 231, rust à 227). Tout le reste est décalé
  de -4 côté rust puis se resynchronise au train x_hat (~708).
- Structures post-sponge IDENTIQUES : [split_field 2 rows][CompleteAdd]
  [VarBaseMul ×51][CompleteAdd][if_/EC][CompleteAdd][opt-sponge train].

### Pistes précises pour la suite (dans l'ordre)
1. **Identifier les 2 points on-curve de jsoo 227-230** : les coeffs
   contiennent `05` (b) → assert_on_curve de 2 points juste avant le
   sponge d'index. Candidats : notre `witness_proof` (openings/messages)
   est appelé AVANT verify → nos checks messages/openings seraient
   ailleurs — REGARDER les labels rust rows 100-226 pour lister
   exactement quels points rust checke pré-sponge, comparer au compte
   jsoo (les 8 demi-gates jsoo en trop). NB : le compte TOTAL Generic
   n'est qu'à +16 (32 halves) — donc rust N'ÉMET PAS certains checks que
   jsoo a, ou les émet en moins ; chercher aussi où rust émet 16 rows de
   PLUS au total (probablement les mêmes blocs déplacés + ~8 halves
   d'écart réel).
2. Le swap de constantes fd033/c0c2f0 autour des gates 704/707 (x_hat
   packed add + blinding add) : matérialisation `cached_constants` de
   coordonnées constantes dans un ordre différent — comparer l'ordre des
   reduce des DEUX CompleteAdd (p1 d'abord chez nous ; OCaml pareil —
   donc la différence vient de QUELLE constante est déjà en cache).
3. Les [Zero,Generic] intercalés du sponge d'index (période 13) : les 2
   demi-rows par permute = réductions des sommes duplex — alignées en
   CONTENU mais décalées de 4 rows par le point 1.

### Méthode validée cette nuit
Comptage de BLOCS de gates customs (endo 32-rows, permutes 11-rows) par
côté = signal fiable et rapide pour localiser les sur/sous-émissions
structurelles ; le diff row-à-row ne sert qu'ensuite. Les fixes
"contenu" (reduce_lincom) se voient dans la classe coeffs, les fixes
"structure" (sg_old vide) dans les histogrammes.

### Dernière découverte de la nuit — comptage des markers on-curve (c=+5)

Comptage des demi-gates dont la constante vaut exactement +5 (le b de
y²=x³+5, marker fiable d'un assert_on_curve) :
- **rust : 51 au total** = VK(28) + messages(23) — les points des
  OPENINGS (lr 32, delta, sg) ne sont PLUS checkés on-curve du tout
  (suite au commit "Align wrap opening point witnesses" qui les a rendus
  unchecked pour aligner le pré-sponge) ;
- **jsoo : 73 au total** = 51 (VK+messages, pré-sponge comme nous)
  + **6 pré-sponge en plus = 2 points = DELTA + SG** (les 4 rows
  227-230 qui décalent tout de -4) + **16 markers TARDIFS aux rows
  4261..5371, espacés EXACTEMENT de 74 rows** = un marker par ROUND
  bulletproof (16 rounds Tick) — les lr sont checkés INLINE dans
  bullet_reduce, un par round (pas 2 — vérifier si c'est L seul, R seul,
  ou une paire fusionnée, en regardant les rows 4261±5 en détail).

**Fix à implémenter (précis, prochaine session)** :
1. dans `witness_proof` (api.rs) : delta et sg witnessés AVEC
   assert_on_curve (revenir à `mkpt` pour ces deux-là), lr reste
   unchecked ;
2. dans `bullet_reduce_challenges`/`bullet_reduce_terms`
   (bulletproof.rs) : émettre l'assert_on_curve d'UN point par round à
   la position jsoo (au début de chaque round, avant/entre les endos —
   caler sur les rows 4261+74k, structure du bloc de 74 rows :
   [marker][2×endo 32][absorb/permute ~8]) — c'est la variante VALIDÉE
   EMPIRIQUEMENT de l'ancienne idée `bullet_reduce_interleaved` (qui
   avait échoué parce qu'elle checkait 2 points par round ET gardait les
   2 sg_old dummies — les deux erreurs sont maintenant comprises).
3. Après ça, l'écart Generic devrait passer de +16 à ~0 : bilan
   +16 rust = -22 markers manquants (16 lr + 6 delta/sg... en halves)
   + les demi-rows de réalignement — re-mesurer après chaque sous-étape.

## Session 2026-07-13 — histogramme et ordre des 8192 gates exacts

Baseline de départ : Generic 571 contre 569, 2702 rows divergentes, première
divergence de type row 230. Quatre corrections sémantiques, mesurées
séparément, ont fermé toute la structure du circuit :

1. `One_hot_vector.of_index` : la fin OCaml `Boolean.Assert.any` n'est pas
   l'égalité linéaire `branch0 = 1`. Elle appelle `assert_non_zero`, témoigne
   l'inverse de la somme et émet un R1CS `inv * branch0 = 1`. Le port de ce
   vrai gadget a supprimé la demi-contrainte manquante avant le premier train
   Poseidon. Diff 2702 → 2102, types exacts jusqu'à la row 1954.
2. `Common.ft_comm` : l'expression OCaml calcule le `scale` de droite avant
   les deux additions (ordre d'évaluation OCaml). Rust calculait la première
   somme avant ce scale, déplaçant un CompleteAdd au travers d'un long bloc
   VarBaseMul. Le calcul de `t_scaled` est maintenant antérieur à `sum`.
   Diff 2102 → 1996.
3. `group_map` : `Field.Checked.sqrt` utilise une contrainte `Square`, pas un
   R1CS générique (trois occurrences). Son `Boolean.Assert.any` est aussi un
   unique `assert_non_zero(b1+b2+b3)`, pas `Boolean::any`/`Field.equal` en deux
   R1CS. Cette correction Snarky a fait passer Generic 571 → **569 exact**,
   Zero 3051 → **3053 exact**, et le diff 1996 → 614.
4. `bullet_reduce` : OCaml construit d'abord les 16 termes
   `endo_inv(L_i)+endo(R_i)`, puis réduit le tableau ; Rust intercalait la
   somme courante entre deux rounds. Le port en deux passes a ramené le diff
   614 → 210. Enfin, OCaml calcule `p_prime`/`q` avant d'absorber delta et de
   squeezer `c`; le découpage `prepare_bulletproof_q` puis
   `check_bulletproof_equation_from_q` place ce bloc au bon endroit et ramène
   le diff 210 → **153**.

État actuel mesuré :

- public input 40/40, domaine 8192/8192 ;
- histogrammes exacts : Generic 569, Poseidon 1001, Zero 3053,
  CompleteAdd 258, VarBaseMul 663, EndoMulScalar 184, EndoMul 2464 ;
- **zéro divergence de type** sur les 8192 rows ;
- 153 rows restantes : 93 coefficients, 60 wiring ;
- segments coefficients : 40–44, 47–51, 54–58, 60–64, 67–71,
  73–103, 168–172, 174–178, 594–595, 703, 705–706, 2058,
  2081–2085, 2088–2090, 2096–2101, 5938–5943, 5956 ;
- les divergences wiring isolées/répétées restent notamment aux rows
  12, 53, 66, 167, 697–707, 1328, 2059–2102, puis une série périodique
  dans les rounds bulletproof.

Les trois tentatives ci-dessus ne sont pas des ajustements factices : les
valeurs mathématiques sont inchangées, les tests unitaires group-map et
bulletproof passent, et chaque modification a strictement réduit le diff.
La prochaine phase est exclusivement la parité des lincoms et de l'ordre des
variables témoins ; ne plus modifier le nombre ni l'ordre des types de gates.

### Passe lincom suivante : ordre d'évaluation du group-map

Le `Snarky_group_map.Checked.wrap` OCaml utilise des liaisons simultanées
`let ... and ...` et retourne le tuple `(x, y)`. Les expressions concernées
sont évaluées de droite à gauche : chaque `y_squared` doit rester adjacent à
son `sqrt_flagged`, dans l'ordre y3/y2/y1 ; les deux conjonctions de x3 sont
créées avant celle de x2 ; les multiplications de la coordonnée y sont créées
avant celles de x. Rust regroupait les trois `y_squared`, puis parcourait les
candidats et les coordonnées de gauche à droite.

Le port de cet ordre ne change aucune valeur ni aucun type de gate et conserve
le test group-map, mais réduit strictement le diff wrap **153 → 149** :
type=0, coefficients 93→89, wiring 60. Un premier essai limité à inverser les
champs obligatoires dans le littéral Rust de `choose_key` avait été mesuré à
**149 → 149** ; il a été retiré. Cet essai incomplet ne réordonnait ni les
vecteurs ni l'allocation explicite précédant le littéral ; la passe suivante
explique et corrige ces deux points.

### Passe lincom suivante : calendrier exact de la VK et du group-map

L'analyse des valeurs présentes dans les 56 contraintes `choose_key` a donné
la permutation exacte produite par OCaml. `Step.map` évalue les champs du
record de droite à gauche et les `Vector.map` appliquent leur fonction du
dernier élément au premier. Le port alloue donc explicitement :

1. `endomul_scalar`, `emul`, `mul`, `complete_add`, `psm`, `generic` ;
2. les 15 coefficients en ordre inverse ;
3. le dernier sigma, puis les six premiers sigma en ordre inverse.

Les vecteurs sont ensuite remis dans leur ordre logique avant de construire
`VerificationKeyComm`. Les coordonnées de chaque `Double.map` sont scellées
`y` puis `x`, comme le tuple OCaml. Cette correction est la réduction majeure
de la passe : **141 → 87**, en supprimant les 29 divergences coefficientielles
de la VK et la majorité de la série de wiring périodique dans l'IPA.

Trois détails du group-map ont ensuite été isolés au lieu d'être testés dans
un même patch :

- `alpha_inv` doit conserver l'AST OCaml `(t2 + fu) * t2` : **147 → 146** ;
- les trois `sqrt_flagged` sont alloués `y1`, `y2`, `y3` (gauche à droite),
  contrairement à l'hypothèse précédente : **146 → 141** ;
- dans chacune des coordonnées finales, les produits de sélection sont émis
  `3`, `2`, `1`, puis recombinés dans l'ordre mathématique `1 + 2 + 3` :
  **87 → 84**.

État mesuré après cette passe : public input 40/40, 8192/8192 rows, tous les
histogrammes exacts, zéro divergence de type, **84 rows divergentes**
(52 coefficients, 32 wiring). Segments coefficients : 40–44, 47–51,
54–58, 60–64, 67–71, 73–74, 168–172, 174–178, 594–595, 703, 705–706,
2058, 2095–2096, 5938–5943, 5956. Le wiring restant est concentré aux rows
12, 53, 66, 103, 167, 697–707, 2059, 2073–2076, 2093–2102, puis
5460–5937.

Essais mesurés puis retirés : inversion de l'ordre des deux valeurs interdites
(87 → 87, avec coefficients 54→56), inversion globale des opérandes de
`Boolean.or` (87 → 94), et allocation gauche-à-droite des sélecteurs
`x1/x2/x3` (84 → 84). Ne pas réintroduire ces variantes sans une nouvelle
preuve de localisation.

### Dernière ligne droite : ordre `Checked.assert_all` et réutilisation du digest

La cause commune des sept blocs `Other_field.check` a été identifiée. OCaml
construit chaque `Field.Checked.equal` normalement, mais son
`Checked.assert_all [equals_1; equals_2]` enregistre la liste tail-first dans
ce contexte de check de type. Rust ajoutait systématiquement `equals_1` puis
`equals_2`. Un helper ciblé, utilisé uniquement pour les cinq slots différés
du statement et les deux représentants `z1`/`z2`, conserve le même témoin et
les mêmes équations mais émet `equals_2` puis `equals_1`. Résultat strict :
**84 → 46**, avec coefficients **52 → 17** et wiring 32→29. Le même ordre sur
`which_branch` retire encore une divergence de wiring : **46 → 45**.

La première divergence historique row 12 venait d'une duplication de cvar :
le digest `messages_for_next_step` est déjà le public input `stmt[12]`, mais
Rust réallouait une variable privée égale pour le premier slot du statement
step utilisé par x̂. OCaml réutilise directement le cvar public. Le port de
cette réutilisation supprime les rows divergentes 12 et 103 sans modifier les
gates ni les valeurs, et donne l'état courant **44 rows divergentes** :
17 coefficients, 27 wiring, toujours type=0 et histogrammes exacts.

Segments coefficients restants : 73–74, 594–595, 703, 705–706, 2058,
2095–2096, 5938–5943, 5956. Wiring restant : 697, 699–702, 704, 707, 2059,
2073–2074, 2076, 2093–2094, 2097–2102, 5460, 5562, 5566, 5624–5625,
5727, 5934, 5937.

Essais supplémentaires retirés : inversion du tuple témoin `(r, inv)`
(84→84), inversion des contraintes des six comparaisons de
`finalize_deferred` (45→45), et inversion locale des opérandes des `&&` du
group-map (45→45). La réduction des checks de type ne doit pas être
généralisée à tout `Field.equal` : le step utilise la variante normale et
reste déjà byte-for-byte iso.

## Jalon 2026-07-13 — wrap : 44 divergences → 2 (commit `a5cc3675ab`)

Le commit `a5cc3675ab` réduit le dernier écart structurel du wrap de **44 à
2 lignes**. Les validations à conserver comme baseline sont :

- step : **FULL MATCH** (512/512, histogramme identique) ;
- wrap : public input 40/40, 8192/8192 rows, histogramme strictement
  identique et zéro divergence de type ou de wiring ;
- Rust : `cargo test -p pickles --lib` : **101/101**.

Les corrections qui ont fermé les 42 lignes sont toutes sémantiquement
neutres : ordre `y` puis `x` des scellages et réductions de points, contrainte
booléenne native dans `split_field`, ordre OCaml des operands dans `group_map`,
scellages explicites de deux y négatifs, et ordre tail-first des deux checks
de l'égalité finale bulletproof.

Il reste exactement deux coefficients constants, aux rows **5943** et
**5956**, dans les deux permutations Poseidon terminales. Les types, wires et
toutes les autres coefficients sont égaux. Les trois constantes attendues
côté jsoo sont portées par les Generic précédant les Poseidon rows 5944 et
5957. Elles doivent être attribuées à leur vrai producteur plutôt qu'écrasées
dans `hash_messages`.

Essai explicitement retiré : forcer un état caché Fq dans
`hash_messages_for_next_wrap_proof` (y compris son miroir hors-circuit). Bien
que l'état soit atteint pour deux vecteurs dummy, il déplace les constantes
vers d'autres valeurs et ne ferme pas le diff. Ne pas réintroduire ce cache
sans identifier l'appel précis et le mode duplex OCaml correspondant.

### Producteur des deux dernières rows (instrumenté)

L'instrumentation non intrusive `RunState::with_label` dans `wrap_main` a
tranché la provenance : les deux contraintes Poseidon situées aux rows 5943
et 5956 sont toutes deux sous le label
`wrap_main: new accumulator hash`. Aucun hash d'ancien accumulateur ne
participe au diff du circuit wrap de référence. La mesure instrumentée garde
8192 gates, les histogrammes exacts et les deux seuls écarts coefficientiels.

La comparaison directe de `wrap_hack.ml` donne le prochain port : OCaml ne
choisit pas son état caché à partir de la longueur du vecteur Rust, mais à
l'index `2 - max_proofs_verified`. Il faut donc passer cette arité logique au
hash du nouvel accumulateur et représenter ses états `s0/s1/s2` avec le même
mode duplex. L'essai « supprimer les dummies quand N2 » a régressé à 30 rows :
ne pas le refaire en changeant seulement les données d'entrée.

## Jalon 2026-07-13 — iso complète Step + Wrap

Les deux dernières divergences sont résolues. Leur cause n'était pas le mode
duplex Poseidon ni la sélection du cache `s0/s1/s2`, mais l'ordre des
challenges IPA dummy. Rust tirait bien les mêmes 15 valeurs `chal_1` à
`chal_15` et appliquait le bon endomorphisme, mais les conservait dans l'ordre
des appels. En OCaml, `Pickles_types.Vector.init` expose le vecteur dans
l'ordre inverse. Le vecteur Rust était donc exactement le reverse du vecteur
de référence ; cela changeait uniquement l'état Poseidon constant du nouvel
accumulateur, d'où les deux coefficients différents aux rows 5943 et 5956.

Le correctif consomme toujours le flux `Ro.chal` en avant, puis inverse chaque
vecteur Wrap/Step avant de calculer ses challenges. Un test de régression
compare désormais les 15 challenges Wrap aux vecteurs officiels de
`pickles/test/test_common.ml`.

Validation finale :

- `cargo test -p pickles --lib` : **102/102** ;
- `cargo test -p pickles --test recorded` : **9/9**, y compris N1, N2 et
  la chaîne stable ;
- step : **FULL MATCH**, public input 1/1, gates 512/512, histogramme,
  coefficients et wiring identiques ;
- wrap : **FULL MATCH**, public input 40/40, gates 8192/8192, histogramme,
  coefficients et wiring identiques ;
- smoke test o1js `rust-pickles-zkprogram.ts` : preuve valide, état public
  `88`.

Essai retiré et à ne pas réintroduire : supprimer le padding dummy du nouvel
accumulateur. Cet essai modifie la structure Poseidon et régressait de 2 à 30
rows. Le cache et le padding précédents étaient corrects ; seul l'ordre du
vecteur dummy était fautif.

## Jalon 2026-07-14 — handle récursif N1 chaînable

`RecordedBaseHandle` est généralisé en `RecordedProofHandle` (l'ancien nom
reste un alias compatible). Le handle conserve soit la preuve de base
complète, soit le dernier cycle step/wrap complet avec ses index. La nouvelle
API `prove_recorded_n1_over_keep` accepte les deux formes : base → premier N1,
puis N1 → N1 sans rejouer les circuits ou témoins précédents.

Le chemin stable accepte maintenant une application embarquée différente à
chaque cycle. Les deux passes de stabilisation de la VK partagent la même
closure applicative ; la première tentative sans application dans le
bootstrap produisait une VK différente. Il faut également distinguer l'état
public précédent de l'état produit par la nouvelle application : confondre les
deux casse la finalisation du digest du cycle consommé.

Validation : `cargo check -p pickles` et `cargo test -p pickles --test
recorded --release` : **9/9**, avec un test réel base → N1 → N1 et vérification
standalone du dernier résultat.

## Jalon 2026-07-14 — application N2 sur deux handles de base

Le circuit step width-2 accepte maintenant une `EmbeddedAppMain` et exécute
donc réellement les contraintes du nouvel appel, au lieu de seulement hasher
un `app_state` fourni par l'hôte. `prove_direct_n2_with_app` factorise ce chemin
et `prove_recorded_n2_over_base_handles` l'expose pour deux preuves de base
retenues compatibles.

La première portée N2 exige deux handles de base dont les wrap VK sont
identiques. Le résultat est une preuve N2 sérialisable et vérifiable ; il n'est
pas encore retenu comme entrée d'un cycle N2 suivant.

Validation ciblée : deux preuves `square` retenues sont vérifiées par un step
N2 qui exécute un nouveau circuit `6 * 7 = 42`, puis la preuve finale est
vérifiée standalone avec `ProofsVerified::N2`.

## Jalon 2026-07-14 — index compilés réutilisables N0/N1

`WrapCircuit` et `RecursiveStepCircuit` reçoivent désormais leur witness via
`PrivateInput` au proving au lieu de le capturer dans la valeur compilée du
circuit. `RecordedCompiledBase` conserve les index Step/Wrap finaux après les
deux passes de découverte de VK ; `RecordedCompiledN1` conserve les index du
Step récursif et de son Wrap. Les deux handles prouvent ensuite de nouveaux
witnesses sans reconstruire les index. Les mêmes handles opaques sont exposés
par `kimchi-wasm` et `kimchi-napi`.

Validation : **12/12** tests `recorded` release, dont réutilisation N0 sur deux
witnesses distincts et N1 compilé ; smoke test o1js vert ; Wrap toujours **FULL
MATCH** 8192/8192. Sur AddZkProgram, le proving compilé base+N1 est maintenant
plus rapide en Rust : 8,361 s contre 8,774 s JSOO en WASM et 4,409 s contre
6,042 s en natif.

## Jalon 2026-07-14 — réutilisation de la preuve Step de compilation N1

La preuve Step nécessaire à la construction du witness de compilation Wrap
n'est plus jetée. `RecordedCompiledN1` conserve le Step, le
`PreparedRecursiveWrap`, le witness et la preuve précédente employés à la
compilation. Le premier `prove_keep` correspondant consomme ce pré-calcul et
ne refait que la preuve Wrap. Les appels suivants, ou un premier appel avec un
witness différent, reprennent le chemin normal avec les deux index conservés.
Le test N1 compilé couvre les deux chemins et vérifie les deux preuves.

Le profil natif froid N1 (`PICKLES_PROFILE=1`) localise désormais le coût :

- préparation : **0,036 s** ;
- compilation de l'index Step : **4,340 s** ;
- preuve Step, utile et réutilisée : **1,596 s** ;
- compilation de l'index Wrap : **3,415 s** ;
- total : **9,386 s**.

Sur AddZkProgram sans cache, le total Rust WASM passe de **33,359 s** à
**29,911 s**, et le total Rust natif de **18,020 s** à **16,247 s**. Le temps
de preuve+vérification après compilation reste nettement meilleur que JSOO :
**5,438 s contre 9,262 s** en WASM, et **2,899 s contre 6,236 s** en natif.
Le retard froid restant est donc la génération des deux index, notamment parce
que l'API actuelle compile un Wrap par méthode là où le compilateur Pickles de
programme partage son Wrap entre les branches.

### Multithreading et frontière WASM

Le benchmark Rust WASM à un worker mesure **29,771 s** pour compiler N0,
**80,402 s** pour compiler N1, puis **30,948 s** pour les deux preuves et
vérifications. Avec 16 workers, les mêmes catégories prennent respectivement
**8,780 s**, **15,693 s** et **5,438 s**. Rayon apporte donc déjà un gain
majeur. L'écart avec JSOO n'est pas plus spectaculaire parce que le frontend
OCaml/JS de Snarky/Pickles est mono-thread, mais ses opérations cryptographiques
lourdes (Kimchi, FFT, MSM et prover) appellent déjà le backend Rust WASM/NAPI
parallèle commun.

Le chemin Rust WASM a aussi été vérifié : l'export `kimchi-wasm` entre une fois
dans `rayon::run_in_pool`, puis appelle directement
`pickles::recorded -> recursive_step -> snarky -> kimchi` dans le même module et
la même mémoire WASM. Il n'existe aucun aller-retour JS entre Pickles et
Kimchi. La frontière JS restante est une entrée par compilation/preuve et une
sortie du résultat ; le circuit JSON est parsé une seule fois à la compilation
et le handle opaque conserve les index en mémoire. Le transport décimal du
witness reste optimisable, mais ne peut pas expliquer les secondes de retard
froid observées par le profil.

### Régression SRS découverte pendant la validation

Le contrôle Step a révélé que le cache SRS partagé paniquait lorsque Snarky
passait une taille de domaine inférieure au SRS Mina complet (512 rows pour le
Step N0). Le paramètre de `SnarkyCircuit::srs` décrit le domaine du circuit, pas
la taille cryptographique fixe à imposer à Pickles. `tick_srs` et `tock_srs`
ignorent donc maintenant cette taille de domaine et retournent toujours les
SRS Mina complets 2^16 et 2^15. Après correction : Step **FULL MATCH** 512/512,
Wrap **FULL MATCH** 8192/8192, smoke test o1js vert et test N1 compilé avec
pré-calcul puis witness différent vert.

## Jalon 2026-07-14 — suppression de la seconde compilation Wrap N0

`CompiledBaseCase::compile` recompilait le Wrap après la passe de découverte
de sa VK. Cette seconde passe produisait exactement le même index : les points
de la Wrap VK ne servent qu'au witness et au digest public du Step, tandis que
les contraintes du Step et du Wrap sont déjà définitives. La première passe
conserve maintenant directement ses index Step/Wrap et en dérive les points
de VK utilisés lors des preuves suivantes.

Sur AddZkProgram natif sans cache, `compile init` passe de **3,930 s** à
**3,075 s** et le total Rust froid de **16,247 s** à **15,133 s**. La
compilation N1 ne change pas. Validation : deux witnesses N0 avec les mêmes
index, suite `recorded` complète, Step **FULL MATCH** 512/512 et Wrap **FULL
MATCH** 8192/8192.

Le partage d'un Wrap entre plusieurs méthodes N0/N1 reste une étape distincte.
Le Wrap Rust actuel déroule ses `unfinalized` selon l'arité réelle et encode la
Step VK sélectionnée dans les constantes du circuit. La parité programme OCaml
demande donc un circuit Wrap multi-branches à slots fixes, avec sélection
one-hot des VK et masquage des slots inactifs ; réutiliser directement l'index
N0 pour N1 serait incorrect.

## Jalon 2026-07-14 — transport canonique binaire des witnesses

Les quatre opérations compilées N0/N1 exposent maintenant des variantes
`*_bytes` dans `kimchi-wasm` et `kimchi-napi`. Chaque élément Fp occupe
exactement 32 octets little-endian et est décodé avec
`CanonicalDeserialize` : longueur non multiple de 32 et représentants hors
corps sont rejetés, sans réduction modulaire silencieuse. o1js préfère ces
endpoints lorsqu'ils existent et conserve le chemin décimal comme fallback de
compatibilité.

Les benchmarks natif et WASM sans cache restent dans la variance précédente,
ce qui confirme que le parsing décimal n'expliquait pas les secondes de
compilation. Le bénéfice est surtout une frontière JS/WASM sans chaînes ni
allocations par élément pour les circuits à gros witness. Validation : build
NAPI/WASM, preuve N0/N1 complète sur AddZkProgram, smoke o1js et rejet explicite
d'un bloc Fp non canonique.

## Jalon 2026-07-14 — pré-calculs Pasta immuables partagés

Les challenges IPA dummy Wrap/Step et leur commitment `sg` sont désormais
initialisés une seule fois avec `OnceLock`. Les chemins N1 padded et le witness
du Wrap réutilisent aussi le SRS Tock partagé au lieu de recréer 2^15 points
dans plusieurs gadgets. Les valeurs exposées sont immuables et restent dérivées
des mêmes constantes de protocole ; aucun transcript ni entrée publique ne
change.

Le profil N1 natif passe de **9,386 s** à **9,155 s** sur la compilation froide
mesurée, avec Step/Wrap et preuve standalone inchangés. Cette optimisation
évite surtout les allocations répétées lors des chaînes récursives.

## Jalon 2026-07-14 — validation sûre des index restaurés

En préparation du cache persistant, Snarky sait maintenant rattacher un index
désérialisé à son générateur de witness seulement après avoir recompilé et
comparé exactement public inputs, récursion, domaine, gates, wiring et
coefficients. Un test positif prouve avec l'index restauré et un test négatif
rejette un coefficient de gate modifié.

L'encodage persistant du witness de compilation Wrap doit utiliser un format
canonique dédié : la tentative serde directe a été retirée, car les champs et
domaines Arkworks ne l'implémentent volontairement pas. Ne pas contourner cette
propriété avec une sérialisation mémoire brute ; restaurer les index seuls et
reconstruire les données auxiliaires est la voie retenue.

Le cache N0 est maintenant exposé par NAPI/WASM et branché sur le `Cache`
fichier standard d'o1js. La clé `recorded-base-v1-<sha256>` engage le JSON
canonique complet du circuit et la version du format. Le fichier contient les
index Step/Wrap sans SRS. Les points de VK ne sont pas acceptés depuis le cache :
ils sont recalculés depuis l'index Wrap validé. Au chargement, Snarky reconstruit
les deux circuits avec le witness courant et rejette toute différence avant de
rattacher l'index. Une empreinte SHA-256 distincte couvre aussi les deux index
sérialisés. Une entrée illisible, corrompue ou incompatible devient un cache miss ;
`Cache.None` désactive aussi ce chemin Rust.

Mesure honnête sur AddZkProgram natif 16 workers : miss **3,402 s**, hit fichier
**3,507 s**. L'entrée fait **85 Mio** et sa désérialisation coûte actuellement
autant que le recalcul parallèle. Le cache est donc fonctionnel et sûr, utile
sur des machines où la compilation est plus lente, mais il ne constitue pas
encore un gain sur cette machine. Le prochain travail cache est un encodage
compact/rapide des évaluations ou un cache mémoire inter-programmes ; ne pas
présenter le format rmp actuel comme une accélération universelle.

## Jalon 2026-07-14 — compilation N1 paresseuse et profil WASM

`RecordedCompiledN1::compile` ne génère plus une preuve Step uniquement pour
construire immédiatement l'index Wrap. Il compile l'index Step et diffère la
preuve Step ainsi que l'index Wrap jusqu'au premier `prove`; les appels suivants
réutilisent les deux index. Sur AddZkProgram natif sans cache, `compile update`
passe ainsi d'environ **9,2 s** à **4,5 s**. Ce changement rapproche le cycle de
vie de l'API Pickles OCaml, où les clés sont paresseuses, sans changer les
preuves ni leur vérification.

Le frontend Snarky a aussi été allégé sur les chemins chauds : union-find,
variables internes et classes d'équivalence utilisent maintenant des indices
denses; la réduction des combinaisons linéaires trie et compacte un petit
`Vec` au lieu de créer une `HashMap` par contrainte; les labels Generic
intermédiaires et l'historique complet des localisations ne sont plus alloués.
Les variables `SNARKY_LOG_CONSTRAINTS`, `SNARKY_LOG_PENDING_GENERIC` et
`SNARKY_LOG_HL_CONSTRAINTS` ont été retirées des boucles chaudes : les lectures
répétées de l'environnement causaient une régression WASM importante. Une
instrumentation par phase, appelée seulement quatre fois par compilation,
reste disponible pour localiser lowering, construction du CS, Lagrange et
index Kimchi.

Le build release `kimchi-wasm` applique désormais automatiquement
`wasm-opt -O4` avec threads et bulk-memory. L'artefact passe de **29 Mio** à
**11 Mio**, ce qui améliore le téléchargement et l'instanciation navigateur,
mais ne réduit presque pas le temps N0 sur cette machine (**7,23 s** à
**7,21 s**). Ce n'était donc pas la cause du retard N1.

État mesuré : N0 Rust WASM reste plus rapide que JSOO WASM à froid
(**7,21 s** contre **9,06 s** pour compiler), tandis que la compilation N1
directe dépasse encore la borne de 30 s en WASM malgré un domaine seulement
égal à 2^14. À 16 workers le processus garde environ **1,7 Gio RSS** et utilise
les workers, mais le frontend récursif reste le goulot. Ne pas reprendre les
micro-optimisations au hasard : utiliser le profil par phase, puis porter le
modèle programme de `Pickles.compile` (branches compilées ensemble, Step
indépendant d'une preuve concrète, Wrap partagé) au lieu de conserver
`compileN1Over(previousProof)` comme architecture finale.

Validation du jalon : les 18 tests Snarky passent; N0 prouve et vérifie; N1
prouve deux fois en réutilisant Step/Wrap; N2 prouve sur deux bases conservées
et exécute la nouvelle application. Tous ces tests release sont verts.

Correctif supplémentaire après ce jalon : `FieldVar::to_constant_and_terms`
construisait un nouveau `Vec` et recopiait les termes accumulés à chaque feuille
de l'AST, donnant un coût quadratique pour les longues expressions linéaires.
Le parcours utilise maintenant un accumulateur mutable O(n). La compilation N1
native descend de **4,35 s** à **1,99 s** et le test N2 complet de **27,06 s**
à **17,16 s** sur les mesures voisines. N0/N1/N2 et les 18 tests Snarky restent
verts. En WASM, le lowering N1 dépasse encore la borne : ce correctif est réel
mais une seconde source spécifique au frontend récursif reste à localiser.

## Jalon 2026-07-14 — socle Wrap multibranche N0/N1/N2

Le chemin récursif largeur deux utilise désormais les mêmes slots physiques
pour les trois arités : N0 `[dummy, dummy]`, N1 `[dummy, real]` et N2
`[real, real]`. Le point manquant était le masque de récursion côté prover :
Kimchi savait déjà produire un proof transcript avec des accumulateurs
optionnels, mais `recursive_step` appelait encore `prove_with_recursion` sans
masque alors que le Wrap vérifiait avec ce masque. Le Step appelle maintenant
`prove_with_recursion_mask`, avec les slots dummy désactivés.

Le Wrap conserve deux `unfinalized` physiques pour toutes les branches. Les
slots inactifs ont `should_finalize = false`, mais leurs challenges calculés
restent présents dans le digest du prochain accumulateur, comme dans le
vecteur de taille fixe OCaml. Le calcul de référence IPA applique également le
masque au transcript et retire les commitments inactifs de la combinaison.

Le test `program_wrap_index_is_shared_by_n0_n1_n2` compile trois Step VK,
construit la sélection one-hot, puis prouve et vérifie successivement N0, N1
et N2 avec exactement le même index Wrap de domaine Tock maximal. Les 102
tests unitaires Pickles, le test N1 padded, le test N1 compilé réutilisable et
les checks NAPI/WASM passent. Il reste à exposer ce compilateur de programme
dans `recorded`/NAPI et à faire compiler `ZkProgram` en une seule opération au
lieu de conserver les handles N0/N1/N2 séparés.

## Jalon 2026-07-14 — handle `RecordedCompiledProgram` et preuve N0 partagée

`recorded` possède maintenant un premier vrai handle programme fixe : chaque
méthode N0/N1/N2 compile son propre Step largeur physique deux, tandis qu'un
unique index Wrap maximal contient la sélection one-hot de toutes leurs VK.
La compilation utilise un proof structurel interne indépendant des contraintes
utilisateur, puis effectue les passes de point fixe nécessaires : Wrap
bootstrap, proof structurel rattaché à la VK Wrap obtenue, Step finaux, puis
Wrap final et vérification de stabilité des VK Step.

Le test `recorded_program_compiles_n0_n1_n2_with_one_wrap_key` compile les trois
arités, prouve réellement la branche N0 avec `[dummy, dummy]`, réutilise le
Wrap partagé et vérifie l'enveloppe standalone avec les messages physiques.
La prochaine étape est d'étendre ce même handle aux preuves N1/N2 consommant
des handles programme, puis seulement d'exposer le handle par NAPI/WASM et
`mina-runtime`; ne pas revenir aux trois Wrap séparés pour simplifier le port.

## Handoff 2026-07-14 — essais N1/N2 du handle programme

L'état poussé reste volontairement le dernier jalon vert :
`RecordedCompiledProgram` compile toutes les branches Step, partage une seule
Wrap VK et prouve/vérifie N0. Les modifications N1/N2 décrites ci-dessous ont
été restaurées après les tests en échec; ne pas supposer qu'elles se trouvent
encore dans les sources.

Validations vertes avant les essais :

- `recorded_program_compiles_n0_n1_n2_with_one_wrap_key` avec preuve N0 et
  vérification standalone : vert en environ 299 s en debug;
- `recorded_compilation_does_not_require_a_satisfying_witness` : vert en
  35,54 s;
- `program_wrap_index_is_shared_by_n0_n1_n2` : N0/N1/N2 verts avec le même
  index Wrap en 236,25 s;
- `cargo check -p pickles -p kimchi-napi -p kimchi_wasm` : vert.

Essais effectués pour faire consommer des handles programme par N1/N2 :

1. Reconstruction directe d'un `PreparedRecursiveStep` depuis le Step width-2
   et le Wrap précédents, avec propagation des deux accumulateurs/challenges
   physiques. Le premier N1 échoue sur `finalize: xi`.
2. Rejeu du masque Kimchi du proof précédent dans
   `oracles_with_recursion_mask` (`[false,false]`, `[false,true]` ou
   `[true,true]`) puis filtrage de `finalize_prev_challenges` aux seuls slots
   actifs. Cela dépasse l'erreur `xi`, mais révèle que l'index N1 avait été
   compilé avec une forme de base sans les deux anciens messages : dépassement
   du witness Snarky autour de l'index 267270.
3. Compilation eager des Step N1/N2 avec un vrai cycle width-2 structurel.
   L'écart tombe à trois cellules (`index 267273` pour une taille 267270). La
   cause est `share_index_sponge` : le cycle provisoire vérifie une Wrap VK
   différente de la prochaine VK (`false`), tandis qu'un vrai cycle du
   programme réutilise l'unique Wrap VK (`true`).
4. Tentative de reprover le cycle structurel avec l'index Wrap final avant la
   compilation définitive des Step. La réutilisation de cet index avec les
   données de branche structurelles n'est pas valide :
   `DisconnectedWires(Wire { row: 91, col: 5 }, Wire { row: 4224, col: 3 })`.
   Cet essai a donc été restauré, pas contourné.

Piste prioritaire pour la reprise : lors de la **compilation seulement** du
gabarit N1/N2, fournir comme `previous_messages_vk_pts` les points de la VK du
Wrap structurel effectivement vérifié. Cela force la même forme
`share_index_sponge=true` que le runtime sans tenter de prouver un witness
contre un index câblé pour une autre sélection de branche. Le gabarit de
compilation n'a pas besoin d'être satisfaisant; le proving réel continuera à
utiliser les messages authentiques du handle précédent. Vérifier d'abord que
le nombre de variables/contraintes du Step compilé est identique au Step N1
réel, puis relancer le test complet N0 -> N1 -> N2. Une fois vert seulement,
exposer le handle partagé dans NAPI/WASM et `mina-runtime`.

## Handoff 2026-07-15 — audit du gabarit programme N1 (essais revertés)

Le dépôt a été remis au dernier jalon vert `a82b053792` après les essais :
aucune API N1 expérimentale ni aucun contournement d'index n'est conservé.

Résultats établis :

- rejouer le masque Kimchi physique du Step précédent et ne transmettre à
  `finalize_prev_challenges` que les slots actifs dépasse bien l'ancien échec
  `finalize: xi` ;
- les challenges du digest précédent doivent être les challenges **calculés**
  de `step.proof.prev_challenges`, pas les pré-challenges sérialisés de
  `messages_for_next_step_proof.old_bulletproof_challenges` ; les confondre
  produit un digest faux ;
- compiler N1/N2 depuis un vrai couple Step-width-2/Wrap structurel, en donnant
  comme `previous_messages_vk_pts` la VK du Wrap structurel effectivement
  vérifié, ferme l'écart de trois variables lié à `share_index_sponge` et le
  test de compilation N0/N1/N2 reste vert ;
- un vrai proving N1 atteint alors le Wrap, mais l'index Wrap N0 partagé donne
  `DisconnectedWires`. Une compilation fraîche du même Wrap N1 prouve, ce qui
  localise le reste dans la **forme du Wrap partagé**, pas dans la preuve Step
  ni dans une vérification Snarky à désactiver ;
- comparaison directe : N0 et N1 ont 32768 gates, mais leur wiring diverge dès
  la row publique 5. La cible de permutation passe approximativement de la row
  8727 (N0) à 9091 (N1). La cause structurelle est le hash de l'accumulateur
  précédent : le dummy de base utilise `hash_dummy_challenges` comme constantes,
  tandis qu'un cycle programme utilise `hash_old_bulletproof_challenges` comme
  variables. Les valeurs peuvent être identiques, mais le calendrier de cvars
  et donc la permutation ne le sont pas.

Conclusion de sécurité : ne PAS prouver avec un index Wrap N1 fraîchement
recompilé, ne PAS ignorer `DisconnectedWires`, ne PAS relâcher les assertions
des slots dummy. Il faut porter le modèle OCaml fixe des challenges padding :
deux slots physiques de même typ/cvar pour N0/N1/N2, avec sélection/masquage
protocolaires, puis vérifier gate+wiring+nombre de variables identiques avant
de réexposer `prove_n1`. Le gabarit de compilation peut être insatisfaisant,
comme chez OCaml, mais toute preuve runtime doit satisfaire l'index partagé.

## Handoff 2026-07-15 — audit OCaml du dummy multibranche

Les essais N1/N2 ont de nouveau été entièrement retirés des sources après
diagnostic ; le jalon fonctionnel reste N0 partagé. Le test baseline
`recorded_program_compiles_n0_n1_n2_with_one_wrap_key` et `cargo check -p
pickles` repassent.

L'audit en lecture seule de Mina précise le modèle à porter :

- `compile.ml::max_local_max_proofs_verifieds` calcule une largeur maximale
  par slot. Pour un programme autorisant N0/N1/N2 et se référençant lui-même,
  les largeurs physiques sont `[2; 2]`, y compris sur une branche N0 ;
- `step_main.ml` étend les slots absents avec `Unfinalized.dummy ()` ; ce
  dummy n'est pas un clone d'un proof de base ;
- `unfinalized.ml::Constant.dummy` construit des challenges, évaluations et
  valeurs Plonk déterministes avec le domaine Wrap `proofs_verified:2`, puis
  fixe `should_finalize=false` ;
- `wrap_main.ml` témoigne `old_bp_chals` avec le typ fixe calculé par slot ;
  `Wrap_hack.Checked.hash_messages_for_next_wrap_proof` démarre depuis l'état
  de sponge pré-calculé correspondant au padding et n'absorbe que la largeur
  locale réelle.

Résultats expérimentaux importants :

- rejouer le masque Kimchi, filtrer `finalize_prev_challenges`, utiliser les
  challenges calculés et compiler les Step depuis un cycle structurel ferme
  bien l'écart du Step N1 ;
- remplacer seulement les challenges constants du hash N0 par deux vecteurs
  témoins rend le nombre de variables, les gates, leurs coefficients et le
  wiring Wrap N0/N1 strictement identiques (`first gate difference: None`) ;
- malgré cela, le générateur de witness compilé depuis le faux dummy de base
  rejette N1 avec `DisconnectedWires`, et le générateur compilé depuis N1
  rejette symétriquement N0 (wire publique row 2 vers environ row 9803) ;
- injecter artificiellement les deux vecteurs dans le transcript de
  finalisation est incorrect : l'assertion `wrap_main: finalize unfinalized`
  échoue, comme elle doit le faire ;
- remplacer le faux dummy par un proof structurel cloné ne suffit pas non
  plus. Le calendrier interne reste dépendant de la construction du witness.

Conclusion : la divergence vient bien de notre modèle multibranche incomplet,
pas d'un bypass à ajouter dans Snarky. La prochaine implémentation doit porter
fidèlement `Unfinalized.Constant.dummy`, le typ/request `old_bp_chals` de
largeur fixe et les états pré-calculés de `Wrap_hack`; ne pas synthétiser le
dummy depuis un proof existant. Le critère d'acceptation reste une chaîne
réelle N0 -> N1 -> N2 prouvée avec le même index Wrap et vérifiée standalone
après chaque branche, sans recompilation pendant le proving.

## Handoff 2026-07-15 — multibranche N0/N1/N2 terminé

Le port multibranche est maintenant fonctionnel sans relâcher les contrôles
Snarky/Kimchi. La divergence venait du port incomplet, pas d'un bug de sécurité
préexistant dans Snarky.

Invariants désormais alignés sur OCaml :

- Step vérifie seulement la H-list logique, puis lie explicitement les slots
  publics absents aux valeurs canoniques de `Unfinalized.dummy` ;
- les accumulateurs/challenges physiques restent de largeur deux, avec les
  masques N0 `[false,false]`, N1 `[false,true]`, N2 `[true,true]` ;
- Wrap transporte les deux `prev_challenges` Kimchi et le vérificateur
  standalone les reconstruit depuis l'enveloppe réseau ;
- les dummies conservent leurs valeurs cryptographiques déterministes mais
  utilisent les métadonnées publiques de l'index réellement finalisé ;
- les Step VK sont stabilisées sous la Wrap VK finale et un seul index Wrap
  maximal est réutilisé pendant `prove_n0`, `prove_n1` et `prove_n2`.

Validation release avec `RUST_MIN_STACK=31457280` :

- `cargo test -p pickles --release --lib` : 104/104 ;
- `cargo test -p pickles --release --test recursion` : 13/13 ;
- `cargo test -p pickles --release --test recorded` : 16/16, dont une chaîne
  réelle N0 -> N1 -> N2 vérifiée standalone après chaque couche ;
- `cargo test -p pickles --release --test e2e` : 1/1 ;
- `make check-format` et `cargo check -p pickles` : verts.

## Session 2026-07-15 — perf compile + notes de parité

### Compile single-pass (commit `162bd1d16c`)
`RecordedCompiledProgram::compile` : le point fixe 4-passes (4 preuves
template, 4 passes de steps, 3 compiles du wrap) est remplacé par UNE passe —
prouvé équivalent par `program_single_pass_matches_multipass_reference`
(l'ancien corps survit en `compile_multipass_reference`). 48.1s → 16.4s en
natif sur le programme 3-branches. Fondement : les alignements
(`align_program_recursive_*`) ne consomment que des champs STRUCTURELS
(domaines, shifts, tokens de linéarisation, endo), invariants sous les
valeurs de VK ; les valeurs (commitments, digests) ne transitent que par des
slots witness.

### Le vrai chemin du bench o1js n'est PAS le program compile
`ZkProgram.compile` (rust-native) → mina-runtime `compile_program` →
`compile_circuit` PAR MÉTHODE : base compile + `prove_keep` (template) +
`RecordedCompiledN1/N2::compile`. N1::compile exécute TROIS preuves complètes
(bootstrap step, bootstrap wrap, stable step) qui ne servent que de donneurs
de forme. Prochain gros gain : les remplacer par des constructions
shape-only (même argument valeurs-vs-structure que le single-pass), et/ou
migrer o1js vers le chemin programme partagé (un seul wrap comme OCaml).
État : compile 3 méthodes = jsoo 8.0s / rust-native 17.2s (après
parallélisation des branches dans mina-runtime) / rust-wasm 53s.
Prove/verify : rust DÉJÀ plus rapide (1.34s vs 2.42s ; 26ms vs 94ms).

### Référence de parité wrap : attention au kimchi-wasm bundlé
Le dump "jsoo" du diff (`fq_prover_to_json`) passe par le kimchi-wasm bundlé
dans o1js (`node_bindings/kimchi_wasm.cjs`) — historiquement un build
pickle-rs custom (PAS l'artefact upstream). Le "2 rows" documenté plus haut
était mesuré contre un build PÉRIMÉ de cette référence. Reconstruite depuis
HEAD (`npm run build:wasm:node:rust` côté o1js), le diff wrap affiche
**32 rows wiring-only** : PI rows 13-28 (les 16 challenges bulletproof du
statement) + une row par round IPA (4332+74k). À bisecter : représentation
du dump vs vrai écart de wiring. Step reste FULL MATCH.

### Suite session 2026-07-15 — compile sans preuves (modèle OCaml)
OCaml `Pickles.compile` ne prouve JAMAIS (dummies précalculés `Dummy.Ipa`).
Porté : donneurs de preuve « shape-only » (`dummy_kimchi_proof_vesta/pallas`,
`dummy_recursive_step_proof`, `dummy_recursive_wrap_proof`,
`dummy_base_case_proof` dans recursive_step.rs) — points multiples du
générateur, scalaires non nuls, challenges/statements réels depuis les
prepared. Les 4 preuves compile-time éliminées : template base (`donor_handle`),
bootstrap step/wrap N1, stable step N1, width-2 N2. Chaque élimination est
prouvée index-équivalente par un test (recorded.rs tests: n1/n2_proof_free_*,
donor_template_matches_real_template). Deux subtilités de FORME découvertes
par les tests : le wrap de base porte 2 RecursionChallenges (padding
Wrap_hack) ; l'assert `sg == commit(b_poly(chals))` (recursion_challenge) se
satisfait en patchant le sg du donneur depuis les challenges matérialisés du
wrap statement.

Bench compile 3 méthodes : rust-native 24.1→10.3s (jsoo-native 8.0s),
rust-wasm 56.5→37.2s (jsoo-wasm 16.3s). Prove/verify rust déjà devant.
**Gap restant = architectural** : le chemin per-méthode compile ~10 index
(base + N1 4 + N2 2 + wraps par méthode) vs OCaml 3 steps + 1 wrap partagé.
Le chemin programme partagé existe (`RecordedCompiledProgram`, single-pass,
lui aussi encore 3 preuves compile-time à donner) — migrer o1js/mina-runtime
dessus est la suite qui ferme le gap wasm.

## JALON 2026-07-15 — WRAP GATES: FULL MATCH ; VK 26/28

Le `if_(is_base_case, c1, c2)` du challenge bulletproof (step_verifier.rs
verify) était un pattern STEP (step_verifier.ml:1312) appliqué au wrap ; en
base case il se constant-fold et laisse les 16 cellules PI des challenges
hors permutation. OCaml wrap = assert INCONDITIONNEL (wrap_main.ml:515-521,
union PI ↔ challenge dérivé). Fix : `base_case_challenge_bypass:
Option<&Boolean>` — step Some(...) (FULL MATCH conservé), wrap None.
**Résultat : WRAP GATES FULL MATCH (types+coeffs+wiring, 8192/8192).**

VK side-loaded (rust-pickles-vk-parity.ts, forceRecompile ajouté — ATTENTION
le cache disque servait une vieille VK jsoo) : **26/28 commitments égaux**.
Restent sigma[0] et sigma[6] (aucun swap : ne matchent rien en face).

### Piste précise pour les 2 sigmas restants
Les deux chemins RUST divergent entre eux : le chemin dump
(prove_base_case_with_wrap_dump — wrap recompilé avec la wdata "réelle") ==
jsoo ✓ ; le chemin prove (CompiledBaseCase::compile puis prove — RÉUTILISE
l'index wrap compilé avec la wdata bootstrap: points générateurs, z1/z2=0)
diverge sur σ0/σ6 (wiring only, gates/coeffs identiques). Donc une VALEUR de
witness de la wdata influence le WIRING quelque part (probablement un
FieldVar::constant / partage cached_constants sur une valeur qui coïncide en
mode bootstrap — ex. `point = generator` partagé). À faire : test rust qui
compile le wrap via les deux wdata (bootstrap vs réelle) et diffe
gates+wires ; trouver la valeur constante fautive ; la witnesser. Ensuite la
VK rust == VK jsoo (les 28 commitments), et il restera l'enveloppe
('mina-runtime-v1:' vs side-loaded base64) + le hash pour que
verificationKey.hash soit identique dans zkapp-rust.

## JALON 2026-07-15 (suite) — VK rust == VK jsoo, hash on-chain compris

Chaîne complète verte pour les programmes single-method non-récursifs :
- wrap σ0/σ6 : fausse alerte (build wasm périmé) — **VK PARITY: FULL MATCH
  28/28 commitments** après rebuild.
- `SideLoadedVerificationKeyV2::mina_hash()` : Random_oracle salt
  "MinaSideLoadedVk****" + pack_to_fields (56 coords puis les 6 bits one-hot
  packés gauche→droite dans UN field) — validé == verificationKey.hash jsoo.
- Enveloppe canonique exposée partout : pickles
  `RecordedCompiledBase::verification_key_envelope()`, napi/wasm
  `rust_pickles_recorded_base_vk_envelope`, mina-runtime
  CompileCircuitResponse{verificationKeyBase64,verificationKeyHash} ; o1js
  zkprogram (rust) retourne la VK canonique pour les programmes 1-méthode
  pv=0.
- **Gate zkapp-rust `test:vk-parity` : les 4 backends (jsoo/rust ×
  wasm/native) retournent le MÊME hash** pour le programme Square :
  7366579521807958688380708523943536275961244156544953379731585537782625645675.

Reste pour la parité totale (programmes multi-méthodes/récursifs) : le wrap
PROGRAMME partagé (un seul wrap par programme, sélection which_branch, comme
OCaml) côté o1js/mina-runtime + sa parité gate width>0 — le gate 'add' du
test vk-parity reste rouge en attendant et sert de critère.

## Perf compile 2026-07-15 (soir) — rust-native DEVANT jsoo

Trois fixes en chaîne (commits 2e276f1c2d, f848594525, 7994c3a72b) :
1. `RecursiveStepCircuit` (width-1) n'overridait pas `srs()` → SRS 2^16
   recréé + lagrange recalculée À CHAQUE compile N1 (~2.5s). → tick_srs
   partagé. N1 compile 5.2→2.5s.
2. `HashMapCache::get_or_generate` calculait SOUS le mutex global → toutes
   les générations lagrange sérialisées entre elles et bloquant les lookups.
   → OnceLock par clé, générations concurrentes, dédup par clé.
3. Cache DISQUE des bases de Lagrange (~/.cache/pickles-rs, PICKLES_CACHE_DIR)
   chargé/écrit par warm_recursion_caches — l'équivalent du SRS pré-calculé
   que jsoo charge du disque. + kimchi feature "parallel" activée workspace.

Bench AddZkProgram natif (cache lagrange chaud, comme jsoo) :
compile 24.1→**5.7s** (jsoo 8.3) ; prove N0 1.4 (jsoo 2.5) ; N1 2.6 (3.9) ;
N2 5.1-5.5 (5.6) ; verify ~3× plus rapide partout. Gate VK square toujours
vert après tout ça.

### Perf wasm (commit a6690d3b52) + LE chantier restant
- Batch compile wasm (`rust_pickles_compile_recorded_program`, une seule
  traversée wasm, branches en parallèle dans le pool) + seed/persist des
  bases de Lagrange par l'hôte JS (wasm n'a pas de fs) : compile rust-wasm
  31.4→18.4s (jsoo-wasm 16.6).
- **Le reste (N2 wasm 9.7 vs 7.1 jsoo ; compile wasm -2s ; VK de l'Add
  différente) converge sur UN SEUL chantier : le wrap PROGRAMME partagé.**
  jsoo : 3 steps + 1 wrap partagé (width-2, sélection which_branch) ; nous :
  ~10 compilations d'index et un wrap par méthode. Le wrap partagé réduit le
  travail absolu (wasm bat jsoo partout) ET donne UNE VK par programme —
  mais la parité VK multi-méthodes exige AUSSI la parité gate des STEPS
  RÉCURSIFS (les VK steps sont des constantes du wrap) et du wrap width-2 :
  nouvelles surfaces de diff à construire (le FULL MATCH actuel couvre
  step base + wrap width-0). Ordre suggéré : (1) harnais de diff du step
  récursif width-2 vs jsoo, (2) parité step récursif, (3) harnais + parité
  wrap width-2 programme, (4) migration o1js/mina-runtime vers
  RecordedCompiledProgram (single-pass + donors déjà prêts), (5) VK
  canonique multi-méthodes → gate 'add' vert.

## Chantier VK jsoo == rust — état au 2026-07-16 (fin de session 2)

Harnais : `o1js/src/tests/rust-pickles-program-gates-diff.ts`
(`SNARKY_KEEP_LABELS=1 MODE=rust ./run ...` — labels par ligne dans
`/tmp/claude-1000/program-gates-rust.json`, jsoo dans program-gates-jsoo.json).
Technique : « anchor-walk » — tous les types non-Generic servent d'ancres ;
comparer les longueurs de runs Generic entre ancres, étiquetées par nos labels.

FAIT cette session (tous commités/pushés, tests recorded 21/21 verts) :
1. o1js dummy_constraints dans les branches récursives (EMS16/scale5/endo4).
2. NOUVEAU digest accumulateur en hash PLAIN (step_main.ml:549) — l'_opt ne
   sert qu'aux ANCIENS digests ; -1 permutation Poseidon par branche.
3. On-curve (y²=x³+5) des 28 points VK wrap témoins (Inner_curve.typ).
4. x_hat step via multiscale_known (step_verifier.ml:115) : scales groupés,
   corrections hors circuit, flags constants ignorés ; CA aligné exactement.
5. Check 16-bit branch_data (Branch_data.typ ~assert_16_bits) par proof.
6. xi wrap = squeeze_scalar / xi step = squeeze_challenge (FrSpongeInputs.
   xi_constrain_low_bits via ShiftKind). EMS exact partout (1/370/739, 536).
7. finalize_deferred réordonné iso finalize_other_proof : zetaw → sg_evals
   (tout-zeta puis tout-zetaw) → fr-sponge/xi/r → chaînes mortes zeta^2^n
   (le TODO wart d'OCaml, wrap_verifier.ml:1628) → env → ft_eval0 → cip →
   bp-challenges → b → perm.
8. cip = 2 plis de Horner (Common.combined_evaluation) + r·(...), masques
   Opt.Maybe en tête de liste.
9. Lagranges hétéro one-hot sélectionnés+scellés DANS la boucle x_hat du
   wrap (tête 426→158 vs jsoo 167).
10. Sponge d'index wrap-VK émise PAR PROOF dans verify_one APRÈS finalize
    (step_main.ml:45, le TODO « Don't rehash ») ; PerProofInput porte
    dlog_index.
11. On-curve de TOUS les points témoins per-proof SAUF les lr
    (Bulletproof.typ les laisse nus ; le marqueur par round vient du
    exists G.typ de endo_inv). stmt/branch_data témoignés APRÈS les points
    du wrap_proof (ordre Per_proof_witness.typ).

ÉTAT : les 4 circuits ont l'ordre des ancres non-Generic IDENTIQUE à jsoo
de bout en bout (init/update/merge/wrap, mismatch@-1). init est 100%
identique en histogramme (168/1/3/1/1/319, 2^10). Restent UNIQUEMENT des
écarts de runs Generic :
- update : 136 sites, net +66 (déplacements ±179/±204 autour de l'intro
  des témoins per-proof — l'ordre INTERNE du bloc de checks doit suivre
  Per_proof_witness.typ exactement ; +53 dans env/linearization/cip ;
  +34 vers recursive_step.rs:4767).
- wrap : 199 sites, net +218 (région finalize +50/proof vers b/perm ;
  jonctions x_hat ±1/±2 packing ; tête -9).
- Les comptes packés (2 gadgets/ligne Generic) ne convergent qu'avec
  l'ordre exact — viser les sites un par un à l'anchor-walk étiqueté.

RÉSOLU (session 3) — la piste opt-sponge a mené à la VRAIE cause,
structurante : **branch_data**. En OCaml (`Branch_data.typ`,
branch_data.ml:135 + `Prefix_mask.Step.typ`, proofs_verified.ml:91) le
per-proof witness contient DIRECTEMENT les 2 booléens de masque préfixe
[b0, b1] (check booléen chacun) + `domain_log2` (check EMS-16), et le champ
packé du statement est la LINCOM `4·dl2 + b0 + 2·b1`
(`Branch_data.Checked.Step.pack`). Encodage wire (`to_bool_vec`) :
N0→0, **N1→2, N2→3** (la valeur 1 = [T,F] est INVALIDE). Nous witnessions
le champ packé + dérivions le masque par 3 equal + any + not/and → d'où :
- les gadgets excédentaires des paires opt-sponge : notre masque
  `first_active = is_zero.not()` était une LINCOM (1−w) — chaque mul/xor
  de l'opt-absorb payait un reduce en plus (rust-only [c,1,c,0,c] =
  reduce de z=Σ−3 avec masque-lincom ; jsoo [-,c,c,0,c] = reduce avec
  masque-var fusionné 2m). Preuve par dérivation complète : paire
  same-var OCaml = 52 gadgets exactement (mesuré jsoo = 52).
- une part du gap witness-intro (±179/±204) : 2 lignes booléennes + EMS
  sur dl2 au lieu d'EMS sur le packé + toute la dérivation.
- `domain_for_compiled` (step_verifier.ml:876-887) : les equal du
  pseudo-domaine s'émettent DANS finalize (entre conversions scalaires
  plonk et zetaw) — déplacés via `FinalizeDomain::SelectFrom` matérialisé
  en tête de finalize_deferred (avant : émis très tôt, avant les evals).
- wrap_main.ml:180-189 : le wrap assert `pack{rev(mask); dl2} == branch_data`
  → lincom `4·dl2 + mask[1] + 2·mask[0]` (api.rs), plus de pv littéral.
Fichiers : composition_types.rs (pack/unpack préfixe), mina_bin_prot.rs
(decode {0,2,3}, rejet 1), recursive_step.rs (witness b0/b1/dl2 à la
position Per_proof_witness, masque = les booléens witnessés, lincom pack),
api.rs (wrap pack), finalize.rs + ft_eval_circuit.rs (SelectFrom).
Primitives vérifiées iso au passage : if_ = 4 gadgets (reduce b-lincom +
2 reduces 2-termes + mul) des deux côtés ; all3 = 7 ; or = 3 ; and = 1 ;
xor = 3 ; add_in = 5 ; y*before = 2. Dump isolé :
`SNARKY_KEEP_LABELS=1 cargo test -p pickles dump_consume_pairs -- --nocapture`
(labels par op dans opt_sponge.rs).

Après parité histogramme+ordre : câblage (differing rows → 0), puis les VK
seront identiques (les constantes choose_pt suivent automatiquement).

ÉTAT FIN SESSION 3 (tout pushé jusqu'à « step: no seal on converted
alpha/zeta ») : init differingRows=0 ; update runDiffs 42 net +39
(@764 +8 : +15 muls = la chaîne zeta_to_srs (16 muls) placée en fin d'env
chez nous mais ABSENTE de la fenêtre @764 jsoo — jsoo l'a dans la fenêtre
@892 (le sig-diff @892 montre jsoo +24 muls) ; le c1-00 est équilibré
(241/243) grâce au NON-SEAL d'alpha/zeta) ; merge net +79 (structure @7/@8
résorbée) ; wrap net −95 : (a) ~−85 = blocs opt-sponge @4391+ (« wrap_main:
verify step proof », labels os:add_in_*) : la Transcript::Opt du wrap
absorbe avec flags CONSTANTS chez nous → blocs dégénérés 6 rows (que les
add_in) vs jsoo 10-25 rows : OCaml NE replie PAS Boolean.all/any sur
constantes (la version liste émet equal(3, 1+1+p) même avec flags true_ —
seuls lxor (to_constant) et Checked.mul replient) → aligner notre
opt_sponge/Boolean sur ce profil de repli ; (b) @2354 +56 (CompleteAdd,
jsoo 226/rust 282) à analyser ; (c) ±1 ×~160 = bruit de phase.
@892 update (j113/r120) = fin finalize (b/perm/conjoncts + ~100 rows
non-labellisées) — y déplacer la chaîne zsl n'a PAS suffi la 1re fois
(mesuré +14) mais le sig-diff dit que jsoo y a plus de muls : à réanalyser
finement (la fenêtre a d'autres écarts : -0-01 +10, 11-00 +10, c1-0c +8).
MÉTHODES qui marchent : sig-histogramme par gadget entre ancres
(5 symboles l,r,o,m,c), clustering de positions, perturbation
(delta sensible à quelles cellules), LCS ciblé block_diff.mjs, et
labels par phase (loc | sous-phase).

WRAP OPT-SPONGE (@4391+, ~−85) — CAUSE COMPRISE : OCaml opt-absorbe
sg_old en PAIRES (keep_var, coord) (wrap_verifier.ml:842 mask_g1_opt) ;
dès le premier flag VARIABLE, next_index devient variable POUR TOUJOURS
→ tous les absorbs suivants (même (true, x)) émettent la machinerie
complète (~11 rows/paire, têtes 25/21/17 pendant le rinçage des
constantes). NOUS pré-masquons par muls (keep·x) et absorbons
(true, masked) → p reste CONSTANT → blocs dégénérés 6 rows (que les
add_in). FIX : Transcript::Opt doit absorber (keep, x),(keep, y)
directement (pas de pré-masquage) — ATTENTION à la couche PHYSIQUE :
la sémantique opt = SKIP si keep=0 (l'état n'avance pas) ≠ absorber 0 ;
le prover wrap physique doit absorber la largeur RÉELLE (Vector.trim
Mina) — vérifier prove_with_recursion_mask / le param recursions de
kimchi (notre fork a un recursion_mask maison) pour rester cohérent ;
les recorded tests trancheront.

SESSION 3, suite — **INIT = differingRows 0 (byte-identique, gates+coeffs+
wires)** après : pinning des segments dummy EN FIN de circuit (r-slot,
Equal(Constant,Var) constant-first — les dernières lignes de tout step jsoo)
+ z1/z2 forbidden (commit 98158c95f0). Structure du step jsoo intro enfin
comprise (update rows 77-392) :
  [162 onc = 81 pts (vk 28 + messages 23 + …)] [2 unités z1/z2]
  [delta/sg onc] [bools masque] [EMS dl2] [cpcs onc 4] [**5 unités** =
  Other_field.check des 5 slots Type2 du STATEMENT (perm,zds,zsl,b,cip,
  impls.ml:50-107, ~18 rows/unité : bool odd + 4 equals + any + assert)]
  [16 EMS] [148 gen] [Poseidons index].
Fixes commités ensuite : 5 unités par proof réel (position post-cpcs),
accs = mêmes vars que prev cpcs (OCaml n'a qu'UN champ), flags = constantes
(Features.none — aucune row), next-vk = réutilisation du dlog_index du 1er
proof réel (jsoo ne re-witnesse pas les 28 pts en self-récursion; le bloc
56 rows n'existe qu'en base case), eval_polish réutilise zk_polynomial et
zeta_to_n_minus_1 de l'env (OCaml les calcule UNE fois — on refaisait des
chaînes pow ~15 muls par occurrence d'UnnormalizedLagrangeBasis, source
majeure du +52 step / +159 wrap de la région finalize).
Pièges notés : compute::<Boolean> émet le check booléen (compute_inner
checked) ; forme bool OCaml = Constraint::Boolean ([-0010]) PAS
assert_r1cs(v,v,v) ([001-0]) ; l'« ordre on-curve différent » vu au LCS
n'était que la phase de packing (init=0 le prouve).

DÉCOUVERTE MAJEURE (session 3) — **dérive kimchi upstream vs pin o1js** :
le commit upstream 64129ce4eb (23/02/2026, « kimchi: update endosclmul
gate ») ajoute une 12e contrainte EndoMul `(xp−xr)(xr−xs)·inv = 1`
(colonne inv = w2) APRÈS le pin o1js (nightly 2026-02-05). Toute VK/preuve
jsoo/Mina bake la version 11 contraintes → REVERTÉ sur pickle-rs
(f8fc66979a). Diagnostic : bisect par sélecteur de gate (zéroïsation) +
sonde par perturbation (delta sensible à Index(EndoMul), w2, w4, w4n, w7).
⚠ À CHAQUE rebase/update de kimchi : vérifier qu'aucun gate/linearization
n'a bougé vs le pin (tests scalars_ml_value_matches_kimchi +
scalars_ml_offline_repro le détectent).

LINEARIZATION EN CIRCUIT = l'arbre EXACT du scalars.ml généré (module
pickles/src/scalars_ml.rs, scalars_{tick,tock}.json parsés par
parse_scalars.py — scratchpad session). Sémantique reproduite : partage
par let top-level + ré-expansions internes (shadowing), évaluation
OCaml droite-à-gauche (opérande DROIT d'abord), Field.square (gadget
Square [00-10], ≠ mul [001-0]), pow = récursion Plonk_checks.pow,
if_feature → branche else (Features.none), joint_combiner = 0,
lagrange = (ζⁿ−1)/(ζ−ω^off) avec numérateur partagé et ω^{-4} LAZY.
Le flux Polish de kimchi calcule la même valeur mais avec une séquence
de gadgets différente (~+238 muls / −47 squares / −89 reduces).


⚠ PIÈGE ADDON : le loader de @o1js/mina-runtime-linux-x64 (index.js) charge
`mina_runtime.node`, PAS `index.node` ! Copier target/napi/index.node vers
`mina_runtime.node` (node_modules/@o1js/... ET native/...) sinon le bench
tourne sur un addon périmé (les VK affichées ne bougent pas).

PLAN CHIRURGIE WRAP OPT-SPONGE (précisé) :
- Côté STEP: RIEN à changer (sg_old_mask est constant-true en pratique →
  les mask-muls se replient; OCaml pad_commitments = constantes,
  absorbs pleins — équivalent ✓).
- (1) STEP PROVER (recursive_step.rs:2722): passer les recursions
  TRIMMÉES (init 0, update 1, merge 2 — enlever les slots dummy) et
  mask=None; le transcript step n'absorbe plus de zéros → largeur réelle
  Mina. Le proof.prev_challenges porte le trim (b-polys IPA suivent).
- (2) ORACLES du step proof pour le witness wrap (ligne ~2805):
  oracles_with_recursion_mask → oracles plain (le proof porte le trim).
- (3) WRAP CIRCUIT (incrementally_verify.rs:313-322): remplacer les
  mask-muls sg_old par des absorbs OPT (keep, x), (keep, y) sur
  Transcript::Opt (méthode absorb_opt à ajouter); dès lors next_index
  devient variable et TOUTES les paires suivantes émettent la machinerie
  complète (~11 rows) = le profil jsoo @4391+.
- (4) Vérifier la COMBINAISON des commitments sg_old dans le bulletproof
  wrap (wrap_verifier.ml:649 + combine_split_commitments avec les paires
  (keep, sg)) — notre équivalent doit masquer/sauter le sg dummy quand le
  step proof n'a qu'un b-poly.
- (5) Les données dummy (pasta_ipa_wrap_and_step, donors, templates de
  compile) doivent être régénérées avec les transcripts trimmés (elles
  sont recalculées au vol normalement).
- Arbitre: recorded 21/21 puis measure (wrap @4391+ doit passer de blocs
  6 rows à ~11 rows; net wrap −95 → ~0). Vérifier init RESTE 0.

TENTÉ (session 3) puis REVERTÉ — la chirurgie opt-sponge casse la
cohérence prover/statement. Détail du blocage pour la reprise :
- Fait: (a) wrap circuit opt-absorb (keep,x/y) des sg_old; (b) step
  prover recursions TRIMMÉES + mask None; (c) oracles plain; (d) helper
  padded_step_sg_olds + pad interne from_parts.
- Le multiphase opt-sponge est PROUVÉ correct (nouveau test lib
  `opt_sponge_multiphase_matches_plain`, gardé) : opt-skip ≡ plain-of-kept.
- ÉCHEC: `verify: sponge digest` (wrap) — la beta/gamma/alpha/zeta
  DÉRIVÉES par la reconstruction wrap ≠ les CLAIMED du statement step.
  Cause: le statement step (deferred challenges) est calculé par un
  MIROIR fq OUT-OF-CIRCUIT qui pad encore avec des zéros, alors que le
  kimchi prover trimmé n'absorbe plus rien → le proof step et son
  statement divergent dès qu'on trim. Il FAUT trimmer AUSSI ce miroir
  (chercher où les beta/gamma/etc du step statement sont calculées:
  probablement dans le calcul du wrap witness / unfinalized, via un
  fq_sponge qui rejoue le transcript step — le mettre en cohérence avec
  le prover: soit tout trimmer, soit tout padder-zéros ET faire le wrap
  circuit absorber (true, 0) au lieu d'opt-skip). ⚠ Décision AVANT de
  recommencer: Mina trim VRAIMENT (donc viser le trim partout) — mais
  c'est un changement transverse (prover + oracles + miroir statement +
  dummy/donor data). REVERTÉ pour rester à 21/21; le gap wrap −85 reste
  ouvert. NB pièges confirmés: kimchi/src/prover.rs:314 absorbe des ZÉROS
  pour keep=false (pas skip) — c'est notre padding actuel, cohérent avec
  le wrap circuit actuel (mask-muls → (true,0)). Donc l'état REVERTÉ est
  self-consistent (juste pas iso-jsoo sur ce bloc).

## Session 3 — outil décisif: HISTOGRAMME DE SIGNATURES (5 symboles)

Le meilleur diagnostic découvert cette session: tokeniser chaque ligne
Generic en 2 gadgets de 5 coeffs [l,r,o,m,c] normalisés {0,1,-,c}, faire
l'histogramme GLOBAL des signatures, diffé rust−jsoo. Un couple
symétrique (ex +72 d'une forme / −64 d'une autre qui ne diffèrent que
d'un signe) = UN bug de forme systématique répété, indépendant du
câblage (donc invisible dans differingRows tant que le wiring bouge).
Script inline (voir historique): sigHist sur steps[2].gates.

FIX LANDÉ via cette méthode: `Boolean::all` (snarky/src/boolean.rs) —
OCaml utils.ml:245 = `equal (const n) (sum)` CONSTANTE d'abord → z=n−sum
(`[c,-,-,0,c]`); nous faisions `sum.equal(const)` → z=sum−n
(`[c,1,-,0,c]`). 64 gadgets os:all3 (opt-sponge) + step_main oks +
finalize_all corrigés d'un coup. `any` était déjà correct (`equal(sum,0)`,
sum d'abord — asymétrie OCaml volontaire: all=const-first, any=sum-first).

ÉTAT après ce fix (commit poussé, recorded 21/21, init=0 tenu):
update signature-mismatch total 123 (était ~230). Restants (r−j):
- `001-0` +23 (muls) — dominé par la chaîne zeta_to_srs (16 muls) mal
  placée (@764 vs @892) + résidus.
- `-0-01` +17, `-1-00` +15, `1--00` +15, `11-00` +10 — diffus dans
  opt-sponge (xor1/xor2/cond_permute_if/add_in) + linearization.
- `-0-00` +10 vs `--000` −9 : AUTRE couple sign-flip candidat (5 no-label
  + 4 scale_fast2 h_minus_g add + 1 x_hat blinding) — à traiter comme
  `all` (chercher un equal/sub à opérandes inversés).
- `00-10` −4 / `10-0c` −2 : 2 points on-curve que jsoo vérifie et pas
  nous (fenêtre intro @6) — PAS messages_accumulators (OCaml n'a qu'un
  champ prev_challenge_polynomial_commitments, la réutilisation est
  correcte); rechercher lesquels (candidats: openings.sg vs delta, ou un
  point du wrap_proof witnessé 2× côté jsoo).
MÉTHODE: pour chaque couple, `<sig> by label` (grep coeffs+labels) puis
comparer la formule OCaml du gadget nommé; corriger l'ordre/forme;
recorded 21/21; commit; re-mesurer l'histogramme.

⚠ DIAGNOSTIC PROCESS BLOQUÉ (leçon session 3) : un run `recorded` a pendu
26 min (deadlock, 52 threads en `futex_do_wait`). Le temps CPU cumulé
(`ps aux` colonne TIME) est TROMPEUR — il montrait 5:54 et donnait
l'illusion d'un calcul en cours. VERDICT FIABLE = échantillonner
`/proc/<pid>/stat` (champs 14+15 = jiffies CPU) 2-3× : s'il n'AVANCE PAS
+ `cat /proc/<pid>/wchan` = futex_do_wait → deadlock certain. Comparer
aussi elapsed (`ps -o etime=`) au CPU : 26 min écoulées pour 6 min CPU =
anormal (run recorded normal ≈ 2 min).
⚠ `pgrep -f "<motif>"` MATCHE SA PROPRE LIGNE DE COMMANDE → faux
"STILL RUNNING" avec des PID à elapsed 00:00. Utiliser
`ps -eo pid,comm | awk '$2 ~ /^recorded/'` à la place.
⚠ TOUJOURS lancer recorded avec `timeout -s KILL 420` (le deadlock semble
être un flake de parallélisme, pas lié aux changements de circuit).
