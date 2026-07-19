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

## REPRISE (état exact 2026-07-18 — OBJECTIF CIRCUITS/VK ATTEINT)
**Scores** : init **0/0** ✓✓ ; update **0/0** ✓✓ ; merge **0/0** ✓✓ ; wrap
**0/0** ✓✓. Le dump wrap frais contient 16384 lignes et `full-diff.mjs`
retourne **0 differing rows** (types, coefficients et wires).

`decode_and_diff_add_vk_against_jsoo` retourne **28/28 commitments** :
`sigma[0..6]`, `coefficient[0..14]` et les six sélecteurs matchent tous.
Suites finales : recorded **21/21**, lib **112/112**.

### PISTE PERF WASM (2026-07-18 soir — EN COURS, tâche : compile wasm < jsoo)
Bench 3-modes (`o1js/src/tests/tmp-bench-wasm.ts`, BENCH_BACKEND=rust-wasm|
rust-native|jsoo ; wasm = `setBackend('wasm')+setProofSystemBackend('rust')`) :
compile natif 12.2s / **wasm 29.2s** / jsoo 16.6s ; proves wasm ≈ jsoo (init
4.4 vs 4.6 ✓, update 9.0 vs 6.1 ✗, merge 8.0 vs 7.8 ≈) ; verify wasm 0.03s
(1er appel 1.0s, warmup pool) vs jsoo 0.25s ✓. VK wasm == natif ✓, preuves
verify=true ✓ → **le rust wasm FONCTIONNE**, reste le compile à accélérer.

Fixes landés (commit 566fcab975, −2.9s : 30.7→28.4 mesuré, 29.2 var.) :
- `tick_srs/tock_srs` → `SRS::create_parallel` **cfg(wasm32) SEULEMENT** :
  ~98k group maps étaient SÉRIELS sur le main thread wasm (−3.3s). ⚠️ En
  natif l'initialiseur parallèle sous `OnceLock::get_or_init` AFFAME les
  pools rayon du harnais multi-tests (recorded passait de 107s à >10min,
  processus à 32% d'UN cœur) — gardé `create` sériel hors wasm.
- Cache Lagrange **v2** (`LGB2`, `*.v2.bin`) : points non-compressés NON
  validés, décodage parallèle (`encode/decode_lagrange_basis_raw` dans
  common.rs). Le v1 rmp/serde payait 1 sqrt/point au seed (7.4s pour 122k
  points wasm, PIRE que recalculer). kimchi-wasm seed : v2 + fallback v1.
- o1js TS (NON COMMITTÉ, rust-pickles-recorded.ts) : seed déplacé DANS le
  scope `runRustPickles` (pool actif, browser-safe), lecture fichiers sur le
  main, noms `.v2.bin`, timers `O1JS_PROFILE_COMPILE` détaillés.

Anatomie du compile wasm restant (~28s ; bisect `O1JS_DEBUG_PROGRAM_STAGE=8`,
timings SANS seed) : template base compile 2.4 + **template base prove 3.6** +
**bootstrap N2 prove 2.3** + wrap structure 2.8 + domain probe 3.3 (pv1
prepare 2.7 domine) + steps 4.9-8.3 (selon seed lagrange) + wrap final 1.2 +
**final template prove 4.2**. Les phases wasm ≈ 2-3× le natif (pénalité
per-op wasm, pool 31 threads actif, CPU 50-80%).

Prochains leviers (ordre) :
1. **Embarquer les dummies** (~−7s wasm) : OCaml `Pickles.compile` ne PROUVE
   JAMAIS (constantes `Pickles.Dummy` précalculées). Nous manufacturons
   template+bootstrap à CHAQUE compile. Scopé : seul `BaseCaseProof` (et
   `RecursiveStepProof` bootstrap) à sérialiser — `template_compiled` meurt
   après `.prove(())` (recorded.rs:2869). Champs : ProverProof kimchi (serde
   ✓), VerifierIndexWrapper = kimchi VerifierIndex (serde ✓, SRS skip à
   réinjecter + linearization à reconstruire), WrapStatementMinimalV1 /
   StepMessagesForNextProofV1 (structs simples Fp/Fq, DTO à la main),
   statements [F; N] → Vec. Cache disque `~/.cache/pickles-rs/template-*.bin`
   versionné + seed wasm par bytes (comme lagrange). `final template prove`
   (4.2s) dépend du wrap VK final → reste live.
2. Cache SRS brut (même codec v2, −1-1.5s wasm, tick 6.3MB/tock 3.1MB).
3. **Backend de corps 32x9** (fork openmina d'arkworks, features dans
   mina-rust Cargo.toml `UNCOMMENTED_IN_CI`) : ~2× sur les ops de corps wasm
   — le levier structurel (notre mina-curves n'a PAS la feature ; adoption
   du fork = projet). Long terme, cf. note mémoire « Embedded SRS+Lagrange ».
4. Architecture : compiler les circuits SANS witness (OCaml synthétise les
   contraintes sans valeurs) — supprimerait le besoin des proves au compile.

### CAMPAGNE #13 — +2b-part2a ✓ : prepare_recursive_wrap_n0_arity (neutre)
Le prepare wrap est générique en ACTIVE (slots unfinalized, décomposition du
statement ; padding old-challenges = MAX_PROOFS_VERIFIED protocole). Prend
le RecursiveStepWidth2Proof<..., ACTIVE>. Recorded 22/22.
**RESTE pour 2b-part2 (les 3 morceaux, dans l'ordre)** :
(i) enum de stockage : RecordedCompiledProgram.step_indexes →
    { W2(Vec<Option<Shaped<67,2>>>), W1(Vec<Option<Shaped<34,1>>>) } ;
    consommateurs = prove paths lignes ~3767-3775 (prove n0/n1 wrap flow)
    et ~4031-4066 (variante debug-stage) : y remplacer aussi
    prove_prepared_recursive_step_width2 → _arity et
    prepare_recursive_wrap_n0 → _arity, dispatchés par le match enum.
(ii) genericiser compile_with_debug_stage → compile_shaped<STEP_PI,ACTIVE>
    (pins actuels ::<RECORDED_N2_STEP_STMT_LEN, 2> → ::<STEP_PI, ACTIVE>) ;
    pub fn compile() dispatch max_pv≤1 → <34,1>. Bootstrap W1 : live
    prepare_recursive_step_n0::<...,34>(template) +
    prove_prepared_recursive_step_width2_arity<...,34,1> (blob plus tard).
(iii) validation : MODE=rust tmp-w1-gates-diff → PI 34, histogrammes,
    flat-emit → 0 ; régression bench/add à chaque pas.

### CAMPAGNE #13 — AVANCEMENT : 1 ✓, 2a ✓, 2b-part1 ✓ (e047510093)
✓ 2b-part1 (NEUTRE, gate byte-identique + 22/22) : chaîne step générique en
<STEP_PI, ACTIVE> (build_prepared, branch compile, probe, steps single-pass),
alias RecordedProgramStepIndexesShaped<PI,A>, entrées circuit _arity pour
compile/domain_log2. TOUS les sites d'appel encore épinglés <67, 2>.
**2b-part2 (PROCHAINE SESSION)** — dans l'ordre :
1. Dispatch max_pv dans compile_with_debug_stage : si max_pv==1 → chaîne
   <RECORDED_N1_STEP_STMT_LEN=34, 1>. Le stockage RecordedCompiledProgram.
   step_indexes doit devenir enum { W2(Vec<Option<Shaped<67,2>>>),
   W1(Vec<Option<Shaped<34,1>>>) } + dispatch dans prove_n0/prove_n1 (les
   entrées prove_prepared_..._arity<...,1> existent déjà).
2. Wrap width-1 : prepare_recursive_wrap_n0 est typé sur le bootstrap
   width-2 (RECORDED_N2_STEP_STMT_LEN) — le witness wrap W1 doit porter un
   step_statement de 34 : dériver du bootstrap W2 (recomposer [seg0(32),
   m4nstep recalculé 1-acc, m4nwrap(1)]) ou prouver un bootstrap W1 live
   (puis blob). Vérifier WrapWitnessData (Vec, sans doute data-driven) et
   les masques 1-accumulateur.
3. Validation : MODE=rust tmp-w1-gates-diff → attendu PI 34 d'abord
   (w1-gates-jsoo.json : init 2^9/PI34, update 2^14/PI34, wrap 2^14/PI40),
   puis histogrammes/flat-emit jusqu'à 0 ; bench/add intacts à chaque pas.
Puis volets 2 (gadget side-loaded natif) et 3 (slots zkapp.ts).

### CAMPAGNE #13 — JALONS 2a FAIT (7d4837ea26) ; DESIGN 2b PRÉCIS
✓ 2a : prepare_n0/n1 génériques en arité (A=(PI-1)/(18+WR)) ; à A=1 le slot
actif 0 = REAL (pas de dummy en tête), dummy_slots [false,true], recursions
[real, dummy]. Régression verte (22/22).
**2b — plombage de types (le gros morceau, ~300 lignes)** :
- Le type WRAP est IDENTIQUE aux deux largeurs (WrapCircuit<16, 40>) ✓ ;
  template idem ✓ ; SEUL step_indexes change de type.
- RecordedCompiledProgram.step_indexes → enum { W2(Vec<Option<W2Idx>>),
  W1(Vec<Option<W1Idx>>) } où W1Idx = RecursiveStepWidth2Indexes<16, 15,
  34, 34, 1>.
- Génériser en <const STEP_PI, const ACTIVE> : compile_recorded_program_steps
  (+single_pass), recorded_program_step_branch_domain_log2,
  build_recorded_program_step_prepared(+fixed_for_debug), la boucle finale de
  compile_with_debug_stage, et les prove_n0/n1 du programme (dispatch enum).
  Les literals RECORDED_N2_STEP_STMT_LEN dans ces fns → STEP_PI ; le
  which-prepare (n0/n1/width2) : à ACTIVE=1, pv=2 impossible (assert).
- prepare_recursive_wrap_n0 : reçoit le bootstrap width-2 — pour W1 le
  witness wrap doit porter un step_statement de 34 → dériver du bootstrap
  (recomposer [seg0(32), m4nstep(recalculé sur 1 acc), m4nwrap(1)]) OU
  prouver un bootstrap W1 live (ajouter au blob dummies ensuite).
- Validation : MODE=rust tmp-w1-gates-diff (o1js) → PI 34 attendu, puis
  histogrammes, puis flat-emit ; régression bench/add à chaque étape ;
  w1-gates-jsoo.json = référence (init 2^9 PI34, update 2^14 PI34, wrap 2^14
  PI40).

### CAMPAGNE #13 — JALON 1 FAIT (00741f1b14) ; CARTE DU JALON 2
✓ Jalon 1 : le main de RecursiveStepWidth2Circuit est paramétré par
ACTIVE_PROOFS (boucles 0..A, layout A*32+1+A → 67|34, assert d'entrée).
Neutre à A=2 : bench byte-identique, 22/22, 112/112.
**Jalon 2 — instancier le pipeline à A=1 (max_pv≤1, hors all-N0)** :
- Dispatch dans compile_with_debug_stage sur max_pv (déjà calculé pour le
  donor). RECORDED_N1_STEP_STMT_LEN=34 existe déjà (width1_step_statement_len).
- Circuit : RecursiveStepWidth2Circuit<16, 15, 34, **34**, **1**> (le
  PUBLIC_INPUT_LEN devient 34 ; WIDTH1_INPUT_LEN inchangé 34).
- Préparation : les arrays [RecursiveStepData; 2]/[bool; 2] restent
  physiques (le circuit ne lit que 0..A) ; écrire les assembleurs de
  statement 34 : n0→[dummy(32), m4nstep, m4nwrap_dummy], n1→[real(32),
  m4nstep, m4nwrap_real] (PAS de slot dummy prépendé contrairement au
  prepare_n1 width-2). Réutiliser program_dummy_step_statement_segment.
- Probe/steps/wrap : instancier domain_log2/compile/steps single-pass et
  les aligns à <.., 34, 1> ; le WRAP garde STMT_LEN=40 (mesuré jsoo=40) —
  son WrapWitnessData reçoit des step_statements de 34 (Vec, data-driven) +
  masques 1 accumulateur ; vérifier les absorb (l'ordre m4nwrap 1 digest).
- Provers : prove_n0/prove_n1 du RecordedCompiledProgram en variante A=1
  (prove_prepared_recursive_step_width2_arity<..,1> existe déjà).
- Validation : PI 34 vs sl-gates-jsoo.json, histogrammes, flat-emit, diff 0 ;
  et régression bench/add intacte. PUIS volets 2 (gadget side-loaded natif)
  et 3 (slots zkapp.ts) du plan ci-dessous.

### CAMPAGNE SIDE-LOADED (tâche #13) — SCOPING MESURÉ (2026-07-19)
Harnais : o1js `src/tests/tmp-sideloaded-gates-diff.ts` (MODE=jsoo|rust),
dumps `/tmp/claude-1000/sl-gates-{jsoo,rust}.json` + `sl-branches.json`.
Mesures : step jsoo **PI=34 (WIDTH-1 !)** vs rust PI=67 (width-2 forcé) ;
histogrammes très différents (jsoo step 1923 Generic/2541 Poseidon vs rust
2672/2596 ; wrap jsoo 1540 VarBaseMul vs rust 2417) ; branche rust : pv=1,
**aux=4478** (le `proof.verify(vk)` de DynamicProof a été ENREGISTRÉ comme
contraintes d'app par le recorder — double machinerie au lieu d'un gadget
side-loaded natif), `previous_state_slots=[]` (le chemin SmartContract ne
passe pas par le collecteur de zkprogram.ts).
**Trois volets à exécuter, dans cet ordre :**
1. **WIDTH-1 pour les programmes max-pv=1** : OCaml compile à la largeur du
   programme (width-1 : statement 34 = 17+15+2, wrap étroit 2^14, masques 1
   accumulateur). Le pipeline recorded force width-2 partout (72 usages de
   RECORDED_N2_*). Les primitives width-1 EXISTENT (RecursiveStepCircuit
   legacy, width1_step_statement_len, prepare width-1) — paramétrer
   compile_with_debug_stage/steps/wrap par max_pv. Valider incrémentalement
   contre sl-gates-jsoo.json (PI d'abord, puis histogrammes, puis diff
   positionnel). ⚠️ garder add/bench (width-2) byte-identiques.
2. **Gadget side-loaded NATIF dans le step** : ne PAS enregistrer le verify
   de DynamicProof comme app (o1js TS : détecter side-loaded au recording,
   l'exclure de l'app, le déclarer en méta de branche avec la position de
   l'arg vk) ; côté rust, per-proof input en saveur side-loaded : VK
   witnessée depuis l'ARG (liée, pas re-witnessée), digest+feature flags
   comme OCaml side_loaded.ml, enfant maxPV=0 → wrap 2^13 dans les domaines
   finalize. La machinerie witness-vk existe déjà (les steps traitent déjà
   la wrap VK en witness) — c'est le câblage arg→witness + masques flags.
3. **Slots SmartContract** : le collecteur previous_state_slots est branché
   dans rustPicklesOutputFieldsForMethod (zkprogram) ; les méthodes de
   SmartContract passent par un autre chemin (zkapp.ts) — y brancher le même
   declareRecordedPreviousState (DynamicProof statement fields).
Cibles de validation : PI 34/34, histogrammes égaux, diff positionnel 0,
VK == 2268640726…0736392 (jsoo stock+branche), VkParity 2/2 et recorded
22/22 + decode 28/28 inchangés.

### GATE ZKAPP-RUST (2026-07-19) : ZkPrograms 4/4 ✓ ; side-loaded ✗ (tâche #13)
`zkapp-rust/contracts` : `test:vk-parity` **2/2** — square (width-0) et add
(récursif) donnent le MÊME hash de VK sur les 4 backends (jsoo-wasm,
jsoo-natif [o1js 2.15 STOCK npm], rust-wasm, rust-natif). `npm test` 2/2
(settlement du proof sur le smart contract Add). MAIS le check side-loaded
(`SideLoadedVkParityChild.js`, SmartContract vérifiant une DynamicProof
contre une VK side-loaded) DIVERGE : jsoo 2268640726…0736392 vs rust
1672172702…3223857 (chacun cohérent wasm/natif). Isolation : branche-jsoo ==
stock-2.15 → pas de dérive TS, c'est le GADGET SIDE-LOADED rust en circuit
qui n'est pas aligné. Repro + méthode dans la tâche #13.

### NUIT 2026-07-18/19 — VK UNIVERSELLE ✓ + WASM SOUS JSOO ✓ (commit 3c060e490d)
**VK universelle atteinte** : BenchNativeProgram (corps app arbitraire :
add(var), assertEquals(0), delta privé) = **byte-identique rust==jsoo sur
les 4 circuits** (était 24/28). AddProgram inchangé (== o1js 2.15 stock).
Cross-verify jsoo⇄rust true. Trois causes corrigées :
1. **App AVANT la machinerie** (recursive_step.rs) : OCaml exécute rule.main
   D'ABORD (step_main.ml) — les statements précédents arrivent en arguments
   (witnessés à l'entrée, sans gates) et les gates de l'app précèdent le
   vérifieur. Le circuit width-2 witnesse les prev app states à l'entrée,
   exécute l'app, et passe les MÊMES vars à recursive_per_proof_input
   (param prealloc). update 419→2 lignes. (Chemin width-1 legacy inchangé.)
2. **previous_state_slots** (recorder o1js + replay rust) : l'heuristique de
   layout (aux == 1+prev) cassait dès qu'une règle avait d'autres inputs
   privés (le delta) → copies fraîches = classes scindées. Le recorder émet
   [(dense, flat)] (ids des champs de statement des SelfProof témoins,
   traduits en indices denses) ; le replay lie ces slots aux vars
   pré-witnessées. Heuristique gardée en fallback (vieilles fixtures).
   update 2→0, merge 3→0.
3. **SRS sauvage dans prepare_n1** (l'« anomalie pv1 » 2,86 s vs 0,17) :
   `SRS::<Vesta>::create(2^16)` NEUF à chaque appel (compile ET prove !) au
   lieu du `pasta_dummy_step_sg()` caché existant ; idem MSM constant dans
   n0. → compile wasm 18,7→**13,0 s** (SOUS jsoo 17,0 froid ✓ objectif
   tâche #10), natif 8,1→**6,2 s** ; prove N1 natif 3,65→2,55 s.
Bench final (froid, Cache.None, 32 cœurs) : compile natif 6,2 / wasm 13,0 /
jsoo 17,0 ; proves wasm ≈ jsoo (init 5,4 vs 4,7 ; update 6,7 vs 6,3 ;
merge 8,5 vs 8,2) ; natif TOTAL 15,8 s vs jsoo 40,7 (2,6×).
Audit parallélisme : rayon partout où utile (steps par branche, SRS
create_parallel wasm, pool 31 threads actif 50-80% CPU) ; probes wasm
séquentiels (mémoire) — ok car pv1 réglé. Restant : #12 (cache prover
keys, jsoo warm 6,0 s), 32x9 parqué (règle iso-jsoo).

### DÉCISIONS PERF (2026-07-18, directives utilisateur — règle ISO-JSOO)
Règle : on n'intègre une optimisation QUE si jsoo a la fonctionnalité
équivalente (iso-fonctionnalité ; le gain rust doit venir du parallélisme,
sans sacrifier sécurité/compatibilité).
- **32x9 (fork openmina d'arkworks) : PARQUÉ** — o1js stock ne l'a pas.
  (Note : dans notre repo le MÊME kimchi_wasm sert jsoo et rust-wasm ;
  l'intégrer accélérerait les deux côtés à la fois.)
- **Cache SRS disque : LÉGITIME** — jsoo cache son SRS en standard
  (~/.cache/o1js/srs-fp-65536 + srs-fq-32768, header kind 'srs',
  désactivé par Cache.None). À faire avec le codec v2.
- **DÉCOUVERTE MAJEURE — cache des PROVER KEYS** : avec le cache o1js par
  défaut CHAUD, jsoo compile en **6,0 s** (recharge step-pk/wrap-pk depuis
  le disque) ; le backend rust IGNORE le cache o1js (chaud == froid :
  natif 7,9 s, wasm 18,4 s). C'est LE prochain chantier (tâche #12) : le
  chemin « base » a déjà le motif complet (rust-pickles-recorded.ts:1660-1712,
  cache_key/from_cache_bytes/cache_bytes, kind 'step-pk') — répliquer pour
  RecordedCompiledProgram (sérialiser les prover indexes kimchi, serde dispo,
  réinjection srs/linearization comme template_dummy::fixup_vi).
Matrice mesurée (compile 3 méthodes) : froid jsoo 16,6-18,2 / natif 7,9 /
wasm 18,2-18,7 ; chaud jsoo 6,0 / natif 7,9 / wasm 18,4.
Bench : BENCH_CACHE=default active le cache o1js dans tmp-bench-wasm.ts.

### SOIRÉE 2026-07-18 — PERF COMPILE (3 fixes majeurs landés) + CAUSE VK UNIVERSELLE
**Perf compile** (bench tmp-bench-wasm.ts, 32 cœurs, mesures du soir) :
natif **12,2 → 7,9 s** ; wasm **30,7 → 18,7 s** (jsoo même run 18,2 s ; son
meilleur observé 16,6 s) — VK inchangée (28/28) et cross-verify jsoo⇄rust
true après CHAQUE fix. Commits : 50049b1739 (dummies embarqués), 2627c3c24d
(final template prove supprimé), ab76811aa0 (donor synthétique).
1. **Dummies embarqués** (template_dummy.rs, blob 44,6 KB include_bytes!,
   parité OCaml Pickles.Dummy) : le compile ne PROUVE plus jamais. Générateur
   `generate_template_dummy_blob` (ignored) + garde `template_dummy_blob_is_fresh`
   (digests compile-only). Les valeurs ne touchent aucune constante de circuit.
2. **`final template prove` supprimé** : le template stocké ne sert qu'à
   padder les slots dummy au prove (masqués, messages transportés dans la
   preuve) — le template embarqué (clé bootstrap) suffit. −4,2 s wasm.
3. **Donor wrap synthétique** : les steps ne consomment que la STRUCTURE du
   donor (domaine→lagranges x_hat via SRS partagé, shifts, 28 slots dont les
   VALEURS sont du witness). Le domaine naturel dépend des tailles de
   statement (frontière 2^14/2^15 — la table wrap_domain_log2 ne suffit PAS,
   3 tests l'ont prouvé) → sondé par `SnarkyCircuit::domain_log2` (cs-only).
Anatomie wasm restante (bisect seedé) : structure index 1,9 s (synthèse du
probe + expr_linearization) ; probe domaines 4,0 s (**pv1 prepare 2,86 s vs
pv2 0,17 s — ANOMALIE à creuser**) ; steps 5,6 s ; wrap final 1,3 s ; + SRS
~1,3 s + pool init. Pour battre le meilleur jsoo (16,6) : élucider pv1
prepare, puis 32x9.

**CAUSE de la VK non-universelle (BenchNativeProgram 24/28)** : le corps
applicatif est REJOUÉ via le snarky rust (RecordedApp/EmbeddedAppMain) et
l'ordre d'émission/packing des demi-gates y diverge de jsoo pour certains
motifs (Equal sur somme, constantes). Mesuré (tmp-bench-gates-diff.ts,
dumps bench-gates-*.json) : init 0 diff ; update 419 lignes (287 coeffs,
1re coeff @78 : half1 jsoo=ADD vs rust=MUL, même multiset) ; merge 738 ;
wrap 34 (constantes step-VK). Histogrammes identiques → pur REORDER, même
famille droite-à-gauche que la nuit. Prochain pas : dump labellisé sur
bench-branches.json + boucle rodée. (Tâche #11.)

### VALIDATION BOUT-EN-BOUT o1js (2026-07-18, addon rebuildé au pin d86a9430)
mina-rust `pickle-rs` bumpé → dfbb4075 (lock = proof-systems d86a9430) ;
`npm run build:rust-backend` (PAS yarn — erreur workspace) installe
`mina_runtime.node` frais aux 2 emplacements. Résultats (32 cœurs) :
- **VK AddProgram IDENTIQUE aux 3 sources** : backend rust == jsoo branche ==
  o1js **2.15 stock npm** — hash
  `10959392966233509715748678308838967246207769407061667940269890557862386195723`,
  data 2396 chars byte-identiques (`tmp-vk-dump-add.ts`).
- **Vérification croisée DANS LES DEUX SENS = true** (`tmp-cross-verify.ts`) :
  preuve update produite par rust → `verify` sous backend jsoo : **true** ;
  preuve update authentique de o1js 2.15 stock (`proof-jsoo-update.json`) →
  `verify` sous backend rust : **true**. Critère réseau atteint.
- **Bench `tmp-bench-native.ts`** (compile Cache.None + N0/N1/N2 + verify) :
  rust 12.0s/1.94s/3.60s/3.35s/0.03s (total 22.9s) vs jsoo
  17.5s/5.01s/6.61s/8.55s/0.26s (total 42.4s) → rust ~1.9× global,
  2.6× init, 2.55× merge, ~9× verify. Le prover jsoo branche REFONCTIONNE
  (le crash vanishing-polynomial d'avant n'apparaît plus sur ce flux).
- ⚠️ Résidu 1 : programme au corps applicatif différent
  (`BenchNativeProgram` : init fait `publicInput.assertEquals(0)` etc.) →
  VK **24/28** (σ[6], coeff[0,4,5] divergent, 1er octet 451). L'alignement est
  complet pour AddProgram mais une règle d'émission côté corps app/snarky
  diverge encore. Repro : `tmp-vk-dump.ts` + diff par commitment.
- ⚠️ Résidu 2 : `--test recursion` = 10/13 ; en plus des 2 rouges
  pré-existants, **`pickles_recursive_step_width2` est un NOUVEAU rouge**
  (UnsatisfiedEqualConstraint @2948 « verify: sponge digest »,
  recursive_step.rs:2746) — chemin legacy fixed-arity, witness hors-circuit
  du digest à réaligner sur le nouveau schedule de sponge.

### JALON FINAL : WRAP 20→0 wires, VK 22/28→28/28
Les 20 derniers wires appartenaient à trois manifestations d'une même règle
OCaml droite-à-gauche :
- les hashes `prev_msgs_wrap` sont émis du dernier unfinalized au premier,
  puis le vecteur logique est restauré avant de threader les deux digests dans
  le statement ;
- `old_bp_chals` est lui aussi witnessé droite-à-gauche. Il faut réutiliser
  chaque vecteur logique pour son propre hash : cela produit les mêmes cvars
  croisés observés dans les cycles jsoo sans jamais échanger les valeurs ;
- le vecteur hôte `sg_olds` est stocké en ordre physique inversé, les aliases
  `prev_step_acc` sont croisés, puis le vérificateur remet le vecteur dans
  l'ordre logique. Le miroir hors-circuit continue de calculer le witness dans
  l'ordre logique, donc N1/N2 restent satisfaisables.

Deux derniers détails complètent les six lignes résiduelles : les composantes
`y` puis `x` des deux `Field.if_` de `combine_commitments`, et la constante de
digest dummy programme recalculée avec son type physique normalisé `[2]`.
Le slot width-1 initial n'est plus le placeholder zéro : il porte `d.stmt[11]`.

### JALON : WRAP = 0 coeff, VK 22/28 — paires Lagrange droite-à-gauche
La frontière @4741 était le premier `statement_terms` à domaine sélectionné.
Le multiset des coefficients était déjà identique, mais organisé par groupes
inversés. Deux paires OCaml imbriquées expliquaient exactement la permutation :
- le point `(x,y)` sélectionné scelle **y avant x** ;
- `lagrange_with_correction` produit `(lagrange, correction)`, donc sélectionne
  et scelle la **correction avant le lagrange**.

Après les deux réordonnancements gate-neutres dans `public_input.rs` : wrap
**227→0 coeff**, wires **548→185**, VK **18→22/28**. Une sonde qui inversait
les sets de domaines a aggravé 227→257 et a été revert ; l'appariement logique
branches/domaines était correct. Suites : recorded **21/21**, lib **112/112**.

### Wires wrap : 185→181, frontière 147→174
`prev_step_accs` est témoigné par OCaml avec
`Vector.wrap_typ Inner_curve.typ Max_proofs_verified.n` : les points sont créés
du dernier au premier, puis le vecteur logique est conservé. Rust `mkpts`
allouait les deux points en avant. Cela croisait exactement les cycles des
quatre coordonnées entre les checks on-curve @147..150 et les hashes des
accumulateurs @4021/@4046/@4228/@4241. `mkpts` émet désormais en reverse puis
reverse son résultat. Coeffs wrap toujours 0 ; recorded **21/21**, lib
**112/112**.

### Wires wrap : 81→20, frontière 304→4021 — diagnostic old_bp
Les deux blocs de 15 divergences de finalisation et les 35 lignes des hashes
étaient une seule famille. Les cycles jsoo montrent que le premier bloc
`finalize` @304..485 partage ses challenges avec le **second** accumulator
hash @4034..4215, et inversement pour le second bloc @2134..2315.

La première implémentation croisait les cvars puis les valeurs au niveau
extérieur des deux `unfinalized`. Elle atteignait 20 wires et passait les tests
tant que les digests recalculés n'étaient pas directement threadés, mais elle
était sémantiquement fausse pour N2. Le correctif final alloue simplement les
deux `old_bp_chals` droite-à-gauche puis reverse le résultat logique : chaque
hash réutilise son propre vecteur. Les indices de cvars sont identiques à la
sonde croisée, les valeurs ne le sont jamais. Voir le jalon final ci-dessus.

### Wires wrap : 181→81, frontière 174→304 — threader prev_proof_state
Rust retémoignait presque tout `w.step_statement` avant `x_hat`, alors que le
`prev_statement` OCaml réutilise directement les cvars de
`prev_proof_state`. Le mapping par preuve est maintenant explicite : `cip`,
`b`, `perm`, sponge digest, β/γ/α/ζ/ξ, les 15 bulletproof challenges et
`should_finalize` réutilisent les champs de `unf_deferred`. Seuls les deux
zeta powers, non conservés comme cvars dans cette structure, restent témoins.
Effet direct : **181→93 wires**.

La famille encore en tête @174/@182 révélait ensuite que les deux
`scalar_to_field` avaient des coefficients identiques mais les identités α/ζ
croisées. Le record checked OCaml est évalué droite-à-gauche : convertir ζ
avant α puis assembler les champs logiques donne **93→81 wires** et avance la
frontière @304. Coefficients wrap toujours 0 ; recorded **21/21**, lib
**112/112**.

### JALON : threading direct et dynamique de l'état applicatif — steps 0/0
La dernière famille update 3 / merge 5 venait de deux copies distinctes du
même état applicatif précédent :
- `recursive_per_proof_input` construisait déjà `proof.prev_app_state`, puis
  retémoignait `d.prev_app_state` juste avant son retour ; le `main` recevait
  cette seconde copie. Il retourne désormais exactement les cvars stockées
  dans `PerProofInput` ;
- `EmbeddedAppMain` reçoit la concaténation des états applicatifs des preuves
  réelles, et le replay du programme Add réutilise ces cvars pour ses slots
  aux `[1..]`, comme les arguments directs du `main` OCaml ;
- au prove-time, ces mêmes slots de VALEURS sont remplacés par les
  `app_state` réellement portés par les preuves précédentes avant de calculer
  le nouvel état et le statement. Cela corrige le `DisconnectedWires` de la
  première sonde 0/0 ;
- le threading est reconnu par la forme enregistrée du programme Add
  (`output.len()==2`, `aux_count == 1 + previous_state_len`) afin de préserver
  la sémantique des fixtures `RecordedCircuit` génériques, qui n'encodent pas
  leurs arguments récursifs dans les aux.

Mesure fraîche `posdiff.mjs` : init/update/merge = **0 ligne différente**.
Les deux régressions historiques ciblées repassent, puis suites complètes :
recorded **21/21**, lib **112/112**.

### Fix wires step : 98→3 update, 206→5 merge
Quatre alignements structurels OCaml, tous coefficient-neutres :
- `prev_proof_evals` était alloué au début du builder Rust, alors que
  `Per_proof_witness.typ` le place après le wrap proof et le proof state. Le
  déplacement pur des allocations change les indices de cvars et donc le tri
  `reduce_lincom` : update 98→60, frontière 1280→1885 ; merge 206→119 ;
- `Pseudo.mask` construit ses produits via `Vector.map` droite-à-gauche, puis
  replie le vecteur en ordre logique : update 60→55, merge 119→111 ;
- l'inverse Snarky OCaml câble `b · b_inv = 1` (et non `b_inv · b`) :
  update 55→51, frontière 1886→2445 ; merge 111→103 ;
- les 16 nouveaux bulletproof challenges passent par un `Vector.map` : les
  conversions `scalar_to_field` sont émises du dernier round au premier, puis
  le vecteur logique est restauré avant `b_actual`. Effet massif : update
  **51→3**, merge **103→5**.

Les 8 lignes restantes sont une seule famille : le `main` o1js reçoit
directement les cvars des états applicatifs des preuves précédentes, tandis
que `RecordedApp` retémoigne actuellement les slots auxiliaires correspondants.
Cycles update : `3042.0↔11435.3` et `3055.3↔11435.0` attendus dans jsoo,
self-loops Rust (`old digest opt` ↔ `new digest`).

Sonde importante rejetée : réutiliser directement ces cvars dans le replay
donne bien **0/0 sur les trois steps**, mais les témoins applicatifs statiques
des fixtures de preuve ne sont pas synchronisés avec les états récursifs
dynamiques ; deux recorded échouent en `DisconnectedWires` :
`recorded_program_compiles_n0_n1_n2_with_one_wrap_key` et
`recorded_program_two_field_state_proves_n0_then_n1`. Il faut threader aussi
les VALEURS dynamiques/statement, pas seulement changer le circuit.

Palier sûr : recorded **21/21**, lib **112/112**. Dump wrap frais :
233 coeff (@138), 548 wires (@147). VK toujours 18/28.

### Exemple frontière de capacité o1js 2^16
`pickles/examples/max_gates.rs` construit le step Pickles complet et cherche
par dichotomie le nombre maximal de contraintes Generic applicatives qui
tient dans le SRS Tick/domaine o1js `2^16`. Il inclut donc le PI, les dummy
selectors EC, le hash accumulateur et les ZK rows (pas seulement le user
circuit). Commande :
`cargo run -p pickles --release --example max_gates`.

Mesure actuelle : **130203 demi-gates Generic applicatives** tiennent dans
65536 lignes (deux Generic par ligne), soit environ **435 lignes-equivalent**
réservées par Pickles/Kimchi ; une demi-gate de plus sélectionne `2^17` et
est donc hors limite o1js. L'exemple assert les deux côtés de la frontière.

### Fix wires step : 221→98, frontière update 252→1280
Quatre permutations d'identité, toutes gate/coeff-neutres, isolées par les
cycles de permutation :
- les blocs Type2 d'ouverture étaient attachés `z2,z1` au lieu de `z1,z2`
  (la première cvar jsoo alimente le premier scale RHS) : 221→213, @252→277 ;
- les checks on-curve tardifs étaient `sg,delta` au lieu de `delta,sg` :
  213→207, @277→384 ;
- le couple `map_plonk_to_field` convertit `zeta` avant `alpha` (opérandes
  OCaml droite-à-gauche) : 207→201, @384→433 ;
- les deux `Vector.map` OCaml qui évaluent les anciens challenge polynomials
  émettent leurs éléments droite-à-gauche. Rust itère donc les challenges en
  sens inverse, puis restaure l'ordre logique des deux vecteurs avant le fold :
  201→162, @433→531. L'ancien `masked_cip_entries.reverse()` devient alors
  faux et a été supprimé ;
- le sponge de challenge et `finalize` consomment le même champ OCaml
  `old_bulletproof_challenges`. Le builder programme témoignait deux copies
  (`prev_challenges` et `finalize_prev_challenges`) ; il partage désormais les
  mêmes cvars sur le chemin fixed-width : 162→98, @531→1280. Le chemin legacy
  conserve ses deux champs indépendants.

Merge suit les mêmes corrections : 450→206 wires, frontière 252→1510 ;
coeffs step toujours 0/0/0. Sonde rejetée : n'inverser qu'un seul des deux
`Vector.map` aggrave 196→201 et recule @473→410 ; les deux doivent être
inversés ensemble avec restauration de leur ordre logique. Inverser les
opérandes du fold de permutation `factor * acc` aggrave update 98→105 sans
faire avancer @1280 ; revert. Dump wrap frais : coefficients inchangés à
240/@134, wires **663→591** (première @147). VK toujours 18/28.
recorded **21/21**, lib **112/112**.

### PISTE PREUVES (zkapp-rust / o1js 2.15 stock) — état
- ⚠️ zkapp-rust/contracts/node_modules/o1js = SYMLINK vers ~/Projects/o1js (la
  branche !) — pour du vrai 2.15 : `/tmp/claude-1000/proofdump` (npm i
  o1js@2.15.0) + `dump-proof.mjs` (compile 19s, init 6.5s, update 8s ✓).
- 🎯 **La VK du 2.15 stock est BYTE-IDENTIQUE à notre référence branche**
  (1796/1796) → les preuves 2.15 ciblent exactement la VK qu'on aligne ; la
  cross-vérif (preuve 2.15 → verifier rust) = LE test de fin.
- ⚠️ Le prover jsoo de NOTRE branche crashe (`rest of division by vanishing
  polynomial`) — régression de branche, compile-only OK (dumps valides).
- `Proof.toJSON().proof` o1js = base64 de SEXP OCaml (`((statement((proof…`),
  PAS bin_prot. Reste à faire : mapping sexp → statement aplati + WrapWire
  ProofV1 (parser: /tmp/claude-1000/sexp2json.mjs ; test squelette :
  `stock_jsoo_215_proof_cross_verifies` dans recorded.rs, skip gracieux).
  Assemblage MinaWrapProof : wrap_recursion_commitments = 2× dummy wrap sg
  (constante), challenges = m4nwrap.old_bp ; args verify_side_loaded =
  m4nstep {cpcs, old_bp} + app_state = publicInput++publicOutput.

### Fix m4nwrap RELANDÉ (2026-07-18) : threading du digest public
La famille wire PI66 : rust témoigne une COPIE du digest m4nwrap (sv[11]) et ne
câble jamais le slot PI (self-loop) ; jsoo threade LA VAR DU STATEMENT dans le
wrap-statement (classe {PI66, usages multiscale}). Fix testé : param
`m4nwrap_digest: Option<&FieldVar>` dans recursive_per_proof_input, call-site
`Some(&statement[len*per_proof + 1 + i])` gated `fixed_width_branch_data.is_some()`
→ **wire 66-family résolue (446→444, frontière 66→135), coeffs 0, N2 legacy OK**.

La cause des deux régressions du premier essai est résolue : le builder legacy
mettait volontairement `0` dans le slot public terminal m4nwrap et les chemins
programme N1/N2 le recopiaient sans le remplacer, tandis que `d.stmt[11]`
contenait le digest réel. Le threading reliait donc la bonne cvar à une valeur
publique stale, d'où `verify: sponge digest`. `normalize_program_recursive_step`
synchronise maintenant le slot terminal AVANT son early-return fixed-width et
`prepare_recursive_step_width2` prend les deux valeurs dans `data.stmt[11]`.
Les deux tests anciennement rouges passent ciblés ; dump frais : init 0,
update 444 wires (première @135), merge full-diff 6902 (première @10).

### Wires update (221 après fix des points per-proof) — familles identifiées
1. RÉSOLU : binding des slots SV forward (commit) — cycle(32.0) aligné.
2. Classe {9,255..376,11071,1,3,5,7} vs {63,393.3,393.4} : rust a DEUX classes,
   jsoo UNE — il manque l'union du sf du slot DUMMY (PI63, update est width-2 :
   1 réel + 1 dummy) et de la paire booleanité-393 avec la grande classe.
   Piste : OCaml assert `sf==mv` pour TOUS les slots (y compris dummy,
   mv=false const → union via cached_constants[0]??) — vérifier la valeur des
   odd-bits du proof enregistré (probablement 0 → classe du zéro !).
3. Familles ~135+ (rs:4425, per-proof witness) : un var témoin dont le 1er
   usage diffère — jsoo l'utilise dans `absorb w_comm` (5986), rust dans le
   `combine` (8742) → un seal/copie d'un côté. Buckets: {0:182, 1000:40,
   2000:59, 3000:41, ...} — ~5-6 familles à traiter une par une (méthode :
   cycle-walk + labels).

### Fix witness points du per-proof (2026-07-18) : update 444→221 wires
Le cycle @135 a montré que les checks on-curve avaient le bon compte et les
bonnes positions, mais étaient attachés aux mauvais objets. Décomposition
exacte des 101 marqueurs `c=5` du step update :
- jsoo rows 79..239 = dlog index (28) + messages (23) + LR (30) ;
- rust = dlog index (28) + messages (23) + COPIE VK (28) + sg/delta (2) ;
- jsoo rows 278/280/284/286 = sg/delta (2) + prev cpcs (2) ;
- rust = prev cpcs (2) + COPIE messages accumulators (2) ;
- les 15 marqueurs tardifs `endo_inv` matchaient déjà.

Fix structurel, gate-neutre : `vk` réutilise les cvars de `dlog_index`, les
30 LR passent par `Inner_curve.typ`, sg/delta sont alloués puis checkés aux
anciens emplacements prev-cpcs, et `messages_accumulators` réutilise les
`prev_cpcs` (OCaml n'a qu'un champ). Le simple swap messages avant la copie VK
avait d'abord donné 444→374/frontière 135→181 ; le fix complet donne
**221 wires, première @252, toujours 0 coeff**, merge full-diff 6679.
Réfutation conservée : inverser les champs autonomes de la VK selon l'ordre
du hlist est un no-op bit-à-bit ; ne pas le retenter.
La dédup `messages_accumulators = prev_cpcs` est gatée au chemin programme
`fixed_width_branch_data` : les fixtures legacy N2 portent légitimement deux
vecteurs indépendants (parfois 2 commitments mais 0 challenges). Sans le gate,
5 tests N2 échouaient dans `hash_messages_for_next_step_proof`; avec le gate,
recorded **21/21** et lib **112/112**.

### RÉSOLU : Merge @529 — placement des `proof_must_verify` du H-list N2
Le flatten/LCS a isolé exactement deux demi-gates boolean manquants côté rust :
jsoo @529A et @619A ; les deux booleanités rust correspondantes étaient
tardives @635B et @11330B, créées à l'entrée de chaque `verify_one`.
`step_main.ml` confirme que `proof_must_verify` est un champ du
`Previous_proof_statement.typ` : pour le H-list de deux proofs, ses checks
s'intercalent après chaque groupe Type2. Rust les témoigne maintenant à cet
endroit, les pin à un, puis `step_main` réutilise ces cvars sans re-witness.
Le chemin update à un proof reste volontairement au placement `verify_one`
(il était déjà à 0 coeff ; appliquer uniformément le déplacement crée 515
diffs à partir de 11072).

Effet : frontière merge coeff **529→11314**, frontière wire **10→42** ;
update inchangé 0 coeff / 221 wires. recorded **21/21**, lib **112/112**.

### RÉSOLU : Merge @11314 — conserver la constante de règle pour le fold
@11314, rust avait un Generic `step proof finalized ++ wrap proof verified`
en trop, puis ses 16 `EndoMulScalar` étaient décalés d'une ligne. Cause : le
fix précédent remplaçait `p.must_verify = true` par la cvar témoignée ; le
fold final `verified && finalized || !p.must_verify` ne pouvait donc plus
replier le OR. OCaml distingue implicitement la cvar passée à `verify_one`
de la valeur constante issue de la règle. Ajout de `result_must_verify` dans
`PerProofInput` : la première reste témoignée pour le binding `sf==mv`, la
seconde reste constante true pour le fold.

Effet : merge **0 coeff-diff sur 32768/32768**, et comme les deux steps réels
ont maintenant 0 coeff-diff, leurs wires ont la même frontière @252 : update
221 lignes diff, merge 450. Le point fixe wrap avance 284→240 coeff-diffs,
frontière 90→134 ; VK encore 18/28. `decode_and_diff` confirmé frais ;
recorded **21/21**, lib **112/112**.

Sonde rejetée update @252 : inverser `z2_h` et `z1_g_plus_b_u` dans
`bulletproof.rs` avance la première wire 252→277, mais aggrave 221→226 et
introduit 2 coeff-diffs @10954/@11060 ; patch revert, ne pas le retenter seul.

## 🎉 JALON (2026-07-18 ~fin de nuit) : STEP UPDATE = 0 COEFF-DIFF
**Le circuit step update est BYTE-IDENTIQUE à jsoo en coefficients** (16384
lignes, 0 différente ; init aussi). Restent : 466 wire-diffs update (permutation
— classes d'équivalence/ordre des cycles, 1re à la ligne 9), merge 5481
coeff-diffs (1re @529, le double-boolean p1, cf plus bas), et le wrap (valeurs
step-VK embarquées → convergeront). Derniers fixes de la série :
- `Equal` réduit v2 AVANT v1 (tuple OCaml droite-à-gauche) — snarky
  constraint_system.rs (split_field pack d'abord).
- `add_fast` scelle y AVANT x par point (paire OCaml droite-à-gauche).
- Chemin programme : mv témoin à l'entrée verify_one (booleanité+merge sf) MAIS
  `is_base_case` = CONSTANTE false (les 15 bypass `Field.if_` des bp-challenges
  se replient → égalité = merge de wires, 0 gate) ET le fold
  `ok = and ||| not mv` utilise la CONSTANTE (pas de gates or) — les 3
  coexistent chez jsoo.

## SESSION 2026-07-18 (nuit) — LA MÉTHODE QUI MARCHE + frontière 236→3752

### Boucle gagnante (à continuer telle quelle)
1. `SNARKY_KEEP_LABELS=1 cargo test -p pickles --release --test recorded
   dump_labeled_wrap_for_b_actual_probe -- --ignored` (dump ~11s)
2. mesurer : 1re ligne coeff-divergente (script inline node, cf transcript)
3. `flat-emit.mjs` (/tmp/claude-1000) : flatten des demi-gates en ORDRE
   D'ÉMISSION (B avant A dans une ligne double !) + labels rust par moitié
4. lire le motif → trouver la règle OCaml (presque toujours : évaluation
   DROITE-À-GAUCHE d'un tuple/liste/args, ou un gadget rust en trop/en moins)
5. fix minimal → redump → frontière avance → commit par lots verts.

### Frontière update (1re ligne coeff-diff) : 236→241→277→287→393→539→1935
→1942→2347→2679→**3752**. merge bloqué à **529** (cf ci-dessous). init = 0 ✓.

### Fixes landés cette nuit (commit 0fe030096a + suivants)
- dup `odd.check` wt2 (compute::<Boolean> check déjà) ; paires prev_cpcs/
  msg_acc SANS dédup autour de branch_data ; suppression r1cs booleanité
  should_finalize précoce ; `witness_must_verify` (mv témoin à l'ENTRÉE de
  verify_one, assert sf==mv = merge de wires) ; opt-sponge or/and inversés ;
  ft_numden term2(zeta−1) avant term1 ; `div_snarky` (inv+mul, 2 gates — la
  division snarky OCaml) aux 2 sites source (frac ft_eval0, 1/gen scalars_env)
  [PolishToken garde div_var 1-gate !] ; cip masked : fold ZETAW d'abord
  (`a + r*b` droite-à-gauche) ; suppression de la boucle per-check
  `or(not mv).assert_equals(1)` post-finalize (OCaml n'a QUE le fold ok de
  step_main ; le Boolean.all du finalize = somme + equal(somme,4), déjà OK).

### ⭐ RÉSOLU #1 → PERCÉE SPONGE (commit du seal-à-l'absorb, snarky/poseidon.rs)
Le blocage @3752 a mené à LA découverte structurelle : **sponge_inputs.ml:53
`add_assign = state.(i) <- Utils.seal (state.(i) + x)`** — le sponge circuit de
pickles SCELLE À CHAQUE ABSORB. Rust accumulait des lincoms réduits au permute :
flux identique quand absorb⊣permute adjacents, DIVERGENT sinon. Fix : machine
d'état inline dans `DuplexState::absorb` avec seal par add (seal court-circuite
en 0 gate pour un lincom mono-terme, comme Utils.seal).
**Effet : update 1re divergence 3752 → 5915, TOTAL 4246 → 550 lignes.**
recorded 21/21, init byte-identique.

### Blocage courant #1bis : update @5915 — rotation de 3 demi-gates (multiscale)
Dans `verify wrap proof | multiscale` : jsoo `[2,4,-1],[1,1,-1],[2,1,-1]` vs
rust `[2,1,-1],[2,4,-1],[1,1,-1]`. [2,4,-1]+[1,1,-1] = réduction du lincom pack
branch_data (b0+2b1+4dl2, 3 termes) ; [2,1,-1] = contrainte de halving
`2·half+odd` du scale_fast2 (public_input.rs:263 → scale_fast2_prime). jsoo
réduit le pack AVANT le gate de halving (réduction des args R1CS droite-à-
gauche ?), rust après/avant différemment. Sonde : lire scale_fast2_prime
(plonk_curve_ops.rs) — l'ordre seal-du-scalaire vs émission du halving, et qui
réduit `s` (le pack) à quel moment. NB: l'ordre des TERMES du multiscale est
CORRECT (les lagranges appariés jsoo-recorded prouvent branch_data en dernier).

### (ancienne sonde @3752, résolue ci-dessus)
Cartographie 3740-3900 : structures IDENTIQUES (P×6, G ifs, P×11, P×11, G×1
absorb-sg, P×11, G×2 multiscale…) sauf **1 ligne Generic rust en trop** =
2 demi-ADD `[1,1,-1,0,0]` (label extérieur = `index_sponge.squeeze` dans
incrementally_verify, IndexDigest::SpongeAfterIndex). Après les cond_permute_if
du old-digest, jsoo enchaîne DIRECTEMENT ses 2 permutations Poseidon
(old-digest final + index-digest squeeze) ; rust seal 2 lincoms pending avant.
ÉLIMINÉ par la sonde : (a) pas de seal-par-absorb jsoo (la région build 56
coords ~3400-3740 matche sans seals) ; (b) pas de seal au build (idem) ;
(c) pas de mémoïsation lincom dans plonk_constraint_system (cached_constants =
constantes seulement). RESTE à lire : le Sponge OCaml de pickles
(step_main_inputs.ml / sponge lib) — comment sa `block_cipher`/copy traite les
2 add pending du 56e absorb pour que le squeeze de l'index-copy ne re-réduise
PAS (aliasing d'état mutable dans Sponge.copy ? absorb-eager au 56e ?
of_sponge du chemin old-digest consommant le pending PARTAGÉ ?). Le rust
équivalent devra faire consommer le pending UNE fois (au chemin old-digest) et
faire partir l'index-squeeze de l'état post-permute.

### Blocage courant #2 : merge @529 — la variable partagée v2
jsoo (merge) : 2 booleanités adjacentes ligne 529 [B=v2, A=odd-bool p1-bloc1].
v2 = classe {PI31, PI63 (les 2 slots should_finalize !), 2 gates par bloc SV du
2e groupe (`[0,0,0,1,0]` l=v2 et `[-1,0,-1,0,1]` l=v2), 619.0/619.1, région wt2
witness 255-428}. Donc les DEUX sf sont FUSIONNÉS avec UNE variable témoin
partagée (le shouldVerify o1js unique ?) et les asserts des blocs SV du 2e
groupe passent par v2 (forme différente du 1er groupe !). update n'a PAS ce
motif (1 seul unfinalized). Piste : o1js témoigne UN Bool par règle (pas par
preuve) ; l'allocation (booleanité) tombe entre les 2 groupes ; les asserts
`not any = true` du 2e groupe utilisent v2 (`Boolean.Assert.is_true` avec la
var true partagée ?) — lire comment o1js/pickles passe shouldVerify et comment
`Boolean.Assert.is_true`/`all` se compile quand le RHS est une VAR.

## SESSION 2026-07-17 — percée diagnostic VK + fix ordre pseudo-domaine

### Méthode : empreinte multiset invariante au packing
Outil décisif (bien meilleur que le row-walking) : extraire chaque demi-gate
Generic non-vide comme son vecteur de 5 coeffs `[l,r,o,m,c]`, en faire un
MULTISET par côté (jsoo/rust), et diff. C'est INVARIANT à l'ordre de packing
double-generic → ça isole les vraies différences STRUCTURELLES (compte) et de
VALEUR (coeff swappés), en filtrant le bruit de packing. Scripts dans
`/tmp/claude-1000/` : `wrap-struct-now.mjs`, `step-struct.mjs`, `step-resid.mjs`
(mapping steps rust = **[init, merge, update]**, pas [init,update,merge] !).
Constante clé décodée : `0000000021eb468cdda89409fc98462200…0040` = **−1 mod Fq**.

### Résultats structurels (dumps courants, pas les stale)
- **WRAP : structurellement IDENTIQUE à jsoo** (genHalves Δ0, tous types de
  gate custom identiques, multiset net 0). Les 118 demi-diffs résiduels du wrap
  sont TOUS des VALEURS embarquées de la step-VK (api.rs:806/810 choose_coordinate
  = 111, `x_hat commitment`, `perm`/`ft_comm`) → convergent via le point-fixe
  circulaire quand la STEP converge. Le wrap n'est PAS le problème.
- **STEP init : parfait** (net 0). **STEP update/merge** : ne divergeaient que de
  ~14/~28 demi-gates, TOUS dans le finalize pseudo-domaine (`finalize | zetaw`,
  `| env`, `| perm check`, `domain_for_compiled`).
- ⚠️ Les stale `program-gates-rust.json` (18:47) donnaient un faux −34 ; toujours
  redumper `wrap-labeled-rust.json` (test `dump_labeled_wrap_for_b_actual_probe`,
  avec `SNARKY_KEEP_LABELS=1` pour les labels) avant de mesurer.

### FIX landé (commit 4632a663ff) — one-hot pseudo-domaine right-to-left
`SelectedDomain::create` (ft_eval_circuit.rs) allouait les bits `equal` de gauche
à droite ; OCaml `domain_for_compiled` utilise `Vector.map` dont le `f` s'exécute
de DROITE À GAUCHE (même ordre que le `.rev()` de `choose_pts` api.rs:818). Donc
le bit du PLUS GRAND log2 obtient le plus petit index variable. `reduce_lincom`
ordonne par index croissant → décide comment le générateur masqué `Σ which[i]·ω_i`
apparie ses générateurs de domaine au `× zeta` (zetaw). Rust appariait à l'envers :
`gen(10)`↔`gen(15)` swappés (constantes `8281bb64…`/`3e0f1c3d…`, `c4bec54b…`=gen14
fixe). Fix : allouer les bits de droite à gauche en gardant `which[i]`↔`log2s[i]`.
Effet : update 14/10→10/6, merge 28/20→20/12, init 0. recorded 21/21.
NB : générateurs identiques des 2 côtés (`Domain::new(1<<log2).group_gen`,
cf kimchi-stubs/src/arkworks/pasta_fq.rs:305 = generator_of) — c'était l'ORDRE.

### FIX #2 landé (commit 96eef3169e) — perm check `of_field` + unseal du negate
`finalize | perm check` (finalize.rs:703) : OCaml `derive_plonk` enveloppe le
scalaire perm DÉRIVÉ dans `Shifted_value.of_field ~shift` et `Shifted_value.equal`
compare les reprs shiftées DIRECTEMENT (shifted_value.ml:49 `equal t1 t2`) — au
contraire des checks cip/b qui `to_field` le côté CLAIMED. Rust `to_field`-ait le
claimed repr (×2, l-coeff 2 vs 1 jsoo). Deux parties :
1. `type1_of_field`/`type2_of_field` + `ShiftKind::of_field` ; comparer
   `perm_repr` (brut) contre `of_field(perm_derived)`. → l-coeff 2→1 + const OK.
2. `perm_scalar_circuit` SEALait son `negate(fold)` dans une var fraîche (coeff
   dérivé -1/2 vs +1/2 jsoo). OCaml garde `negate(fold)` en lincom NON-sealé
   (plonk_checks.ml:427). Retourner le lincom ; sealer seulement au site de test
   (ft_eval_circuit.rs:611 câble perm en sortie → besoin d'une var).
Effet : update 10/6→**8/3**, merge 20/12→**16/8**. Classe perm check éliminée.

### ⚠️ Tests recursion (`cargo test -p pickles --test recursion`) : 2 rouges PRÉ-
EXISTANTS (avant cette session, vérifié sur 94c6661b9c) :
`pickles_recursive_step_n1_is_physically_padded` et
`program_wrap_index_is_shared_by_n0_n1_n2` (+ `recursive_wrap_ipa_equation_holds`).
Ce sont des tests de PREUVE réelle qui resteront rouges tant que l'alignement VK
n'est pas complet — PAS une régression des fixes de session. lib 112/112,
recorded 21/21 verts. **Toujours lancer `--test recursion` en plus de recorded
avant de conclure « pas de régression ».**

### PERCÉE OUTIL #2 — le POSITIONAL diff (bien meilleur que le multiset ici)
Le multiset est invariant à l'ordre → il RATE la divergence dominante : le
**WIRING (permutation)**. Utiliser le diff POSITIONNEL (gate[i] vs gate[i],
comme le harness o1js `rust-pickles-program-gates-diff.ts`) :
- `posdiff.mjs` (typ+coeffs+wires), `posdiff-coeff.mjs` (typ+coeffs seul).
Résultats DÉCISIFS (dump courant) :
- **STEP init : 0 lignes différentes = BYTE-IDENTIQUE** (coeffs ET wires). ✓✓
- **STEP update/merge** : structure quasi identique (**seulement −3 lignes
  Generic**, +3 Zero), mais 1re divergence de **TYPE** à la **ligne 279** :
  jsoo `Generic` / rust `EndoMulScalar` (compte EndoMulScalar identique → pur
  REORDER). L'`EndoMulScalar` (label `scalar_to_field | recursive_step.rs:4611`
  = décomposition 16-bit du `domain_log2` de branch_data) est émis 3 lignes trop
  TÔT en rust ; jsoo émet 3 gates Generic on-curve (label 4421) AVANT.
- Le gros du diff (7745 lignes coeff, 8690 wires) est la CASCADE de packing +
  décalage de lignes en aval de ces quelques reorders. Les wires pointant ~3076
  lignes plus loin = variables DIFFÉRENTES (pas un simple décalage), downstream.
- ⚠️ `flush_generic_before_custom` est du CODE MORT (toujours false ; jamais mis
  à true ; le va-et-vient plonk_curve_ops.rs:413-428 est un no-op). OCaml
  `add_row` (plonk_constraint_system.ml:1259) ne flush PAS non plus avant un
  custom gate. Donc le reorder @279 n'est PAS un flush — c'est l'ORDRE d'émission
  des opérations du per-proof witness (branch_data scalar_to_field vs on-curve /
  accumulator 4709) qui diffère. Réf OCaml : per_proof_witness.ml:137-157
  (ordre du typ : Wrap_proof, Proof_state[dont Branch_data.typ:152], All_evals,
  bp-challenges, prev_challenge_polynomial_commitments).

**MÉTHODE À SUIVRE** : itérer « corrige la 1re divergence positionnelle → redump
→ trouve la suivante » (comme l'ancien `differing rows`), PAS le multiset. Le
multiset servait à voir les classes de compte ; le positional voit l'ordre+wires.

### 1re divergence COEFF = ligne 236 (localisée précisément)
Labels rust : 232-235 = `4421`(on-curve mkpt), **236 = `4554 ++ 4421`**. Donc au
row 236, rust émet un gate `4554` (= le witness/check du scalaire z1 dans la
closure `wt2`, recursive_step.rs:4552-4573) là où jsoo émet encore un demi-gate
ON-CURVE (`[0,0,W,1,0]`). C'est la transition **messages(on-curve) → z1(wt2)** :
rust apparie le demi on-curve pending avec le 1er gate de wt2 z1, jsoo l'apparie
avec un autre on-curve. Ordre high-level identique (messages→lr→z_1→z_2→delta→sg,
bulletproof.ml + rust 4576-4585) → c'est un écart de PACKING/parité de demi-gates
(nb de demi-gates par assert_on_curve : x²Square + x³mul + rhs-reduction + y²Square).
W = `00000000ed302d99…0040` = −(0x47afc1f319ba3400000001), 5 = curve b.

### FIX #3 landé (commit 74b006e645) — openings bulletproof right-to-left
Le `Typ` OCaml vérifie les champs d'un record DROITE-À-GAUCHE. Le record
bulletproof `{lr; z_1; z_2; delta; sg}` → OCaml émet les on-curve de `sg` puis
`delta` AVANT les `Other_field` de z_2/z_1. Rust témoinait z1/z2 d'abord → ses 2
points on-curve d'openings tombaient après les gates wt2. Fix : témoin sg, delta,
z2, z1. **1re divergence positionnelle 236 → 241** (delta/sg on-curve byte-match).
+ `forbidden_shifted_values_fp_pairs` trie/dedup les valeurs 255-bit (OCaml
impls.ml:30 `dedup_and_sort`) — neutre pour les constantes pasta actuelles.

### Résidu courant : ligne 241 = wobble de PACKING dans wt2 (z2/z1 Other_field)
Les valeurs forbidden matchent EN ORDRE (jsoo=rust : `01..ff3f`, `00..ff3f`,
`803b..ff1f`). Mais décalage de packing d'1 ligne : jsoo met le 2e forbidden aux
lignes 244-245, rust 245-246, puis RÉALIGNE à 248. Donc rust émet 1 demi-gate de
trop entre forbidden #1 et #2 dans le gadget `equal`/`and` (phase double-generic
qui se corrige seule). Prochaine sonde : compter les demi-gates de
`FieldVar::equal` (cvar.rs:225 `z=self-other`, 2 r1cs) vs OCaml `Field.Checked.equal`
+ le `and`(`b_eq=odd.not()` lincom vs `odd` var) — trouver le demi-gate en trop.
Puis EndoMulScalar @279 (reorder branch_data, cf plus bas).

**SONDE APPROFONDIE @241 (flatten des demi-gates, rows 240-250)** : ce n'est PAS
qu'un wobble de packing — la SÉQUENCE des demi-gates diffère. jsoo émet
`[0,0,0,1,0]` au flat-idx 2, rust au flat-idx 5. Le z-reduction du `equal`
(`[1,0,W,0,<forbidden>]`) apparaît 2× des 2 côtés (les 2 r1cs réduisent z chacun),
mais l'INTERLEAVING equal/and/any diffère. Donc l'ordre d'émission des gadgets
booléens (`FieldVar::equal` cvar.rs:225 + `Boolean::and` + `Boolean::any`
recursive_step.rs:4563-4571) ne matche pas l'ordre OCaml (`Field.Checked.equal` +
`Boolean.(&&)` + `Boolean.any`, impls.ml:95-102). PROCHAIN : comparer demi-gate à
demi-gate la séquence d'UN forbidden (equal→and) rust vs OCaml pour trouver la
transposition, probablement une éval droite-à-gauche (comme les fixes précédents)
dans `and`/`any` ou l'ordre des 2 r1cs de `equal_constraints` (cvar.rs:207-208,
déjà inversé une fois — vérifier si l'inversion doit s'étendre au `and`/`any`).

### ⚠️ BLOCAGE FONDAMENTAL : pas de labels jsoo possibles
Le gate OCaml est `{kind; wired_to; coeffs}` (plonk_constraint_system.ml:1274) —
AUCUN champ label. `with_label` sert aux messages d'erreur, pas stocké par gate.
Donc IMPOSSIBLE de dumper des labels jsoo pour differ. Les divergences de
packing/ordre subtiles (236, 279…) se résolvent UNIQUEMENT par analyse de l'ORDRE
d'émission dans la source OCaml (per_proof_witness.ml, bulletproof.ml, snarky_curve
assert_on_curve, impls.ml Other_field) — pénible mais c'est la seule voie. Les 2
fixes propres de cette session (generator, perm) venaient d'ordres OCaml lisibles ;
236/279 demandent le même travail sur l'émission du per-proof witness.

### Résidu STEP restant (update 8/3 multiset, merge 16/8 — mais le VRAI blocage
est le WIRING/ordre, 1re divergence positionnelle ligne 279 — prochaines sondes)
Petits écarts de COMPTE dans du boilerplate récurrent (plus durs que les swaps
propres, il faut trouver LES instances qui diffèrent) :
- `[1,0,W,0,5]` (W=`00000000ed302d99…0040`, const 5) jsoo 101/rust 99 →
  `recursive_step.rs:4421` (83) + `verify wrap proof | bp reduce` (15).
- `[0,0,1,−1,0]`/`[0,0,−1,1,0]` mul (1695→1694, 252→248), `[1,1,−1,0,0]` add
  (718→720), `[0,0,0,1,−1]` inverse (4→3), `[−1,0,0,1,0]` (43→44).
- ⚠️ RAPPEL : le multiset est invariant à l'ordre → il ne voit PAS les pures
  réordonnances (qui cassent quand même la VK positionnellement). Le vrai juge
  reste `decode_and_diff` (VK réelle, **12/28** — n'avance que quand TOUTE la
  step-VK converge).

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

## Deux métriques, deux AXES différents (leçon clé session 3)

- **Histogramme de signatures** (coeffs normalisés) ne voit QUE la forme
  des coefficients. Il attrape: ordre d'opérandes d'un `equal` (z=a−b vs
  b−a → `[c,1,-,0,c]` vs `[c,-,-,0,c]`), square-vs-mul, lincom scalée.
- **differingRows** (typ+coeffs+wires à index égal) voit AUSSI le câblage.
  Il attrape: ordre d'opérandes d'un `mul` — car `R1CS(x,y,z)` compile en
  `add_generic_constraint ~l:x ~r:y ~o:z [|0;0;s3;-s1*s2;0|]` : swapper
  x/y change QUELLE variable va en l vs r (le wiring) mais PAS les
  coefficients (`001-0` des deux côtés).

⇒ Un fix d'ordre de `mul` est INVISIBLE dans l'histogramme et ne se voit
que dans differingRows. Un fix d'ordre d'`equal` se voit dans les deux.
Mesurer les DEUX après chaque fix.

RÉSULTAT du fix challenge_polynomial (`f i * !r`, terme neuf à gauche):
signature mismatch inchangé (123, attendu) mais differingRows AMÉLIORÉ
partout: update 8367→8345, merge 15898→15885, wrap 11178→11158; init
reste 0. Petit mais réel, et valide l'approche.

PROCHAIN GROS GISEMENT: le **wrap** a 689 de signature-mismatch (5× celui
d'update = 123). Top: `001c0` j2019/r1862 (−157), `c0c01` j187/r79
(−108), `c0c00` j0/r55 (+55), `cc000` j136/r83 (−53), `00100` +36,
`c1c0c` +34, `10c00` +34, `00c00` +34. Ces formes en `c` (coeff
arbitraire) suggèrent des lincoms scalées/masquées — cohérent avec le
chantier opt-sponge wrap (les mask-muls `keep·x` produisent des `c`
partout où jsoo a des opt-absorbs). À traiter APRÈS la décision de design
trim-partout, car les deux se recouvrent.

## ✅ CHIRURGIE OPT-SPONGE WRAP — RÉUSSIE (commit 04e437da4b)

Le blocage de la 1re tentative était le **4e maillon manqué**:
`crate::wrap::wrap_witness` (wrap.rs:~100) est un MIROIR hors-circuit qui
rejoue la transcript Fq pour produire les `claimed` du statement wrap — il
absorbait encore des ZÉROS pour les slots masqués pendant que le prover
trimmé n'absorbait rien ⇒ claimed ≠ derived ⇒ `verify: sponge digest`.
Les 4 maillons DOIVENT bouger ensemble:
 1. step prover: recursions filtrées (trim), mask=None au prove
 2. oracles: sans masque (la preuve trimmée porte la vérité)
 3. circuit wrap: sg_old en opt-absorbs (keep,x)/(keep,y) — PAS de
    pré-masquage keep·x; combinaison = Opt.Maybe côté wrap / Just côté step
 4. wrap_witness: SKIP des slots masqués (pas d'absorb de zéros)
+ re-padding des vecteurs WITNESS à la largeur physique là où le masque
  décide (sg_olds dans from_parts, finalize_prev_challenges).

MÉTHODE QUI A DÉBLOQUÉ: instrumenter les TROIS points à la fois
(oracles kimchi hors-circuit / derived in-circuit / claimed in-circuit).
derived==oracles mais ≠claimed ⇒ le coupable est le miroir, pas le
circuit. En une exécution. (La 1re tentative devinait.)

GAINS: wrap netGeneric −95→+26 ; differingRows 11158→**8992** (−2166) ;
signature-mismatch 689→**317**. init reste 0, update/merge inchangés
(8345/15885). Les pires formes `001c0`(−157)/`c0c01`(−108) ont disparu:
c'étaient bien les mask-muls.

PROCHAIN FILON WRAP: couple sign-flip `c0c00` j0/r55 (+55) vs `cc000`
j136/r83 (−53), dans `scale_fast2 h_minus_g add` (27) + `verify step
proof` (28). Lecture des formes: jsoo émet un **Equal(Var,Var) scalé**
(`[c,c,0,0,0]` = s1·x1 − s2·x2 = 0) là où nous émettons un **reduce_to_v**
(`[c,0,c,0,0]` = s·x − sx = 0). Chercher dans plonk_curve_ops.rs
scale_fast2 / add_fast(h, g.negate()) l'endroit où OCaml fait un
`Field.Assert.equal` de deux lincoms scalées au lieu de matérialiser une
variable scalée. Puis `c1c0c` +36 (finalize/ft_eval0/env).

## ✅ add_fast seal (commit suivant 04e437da4b) — wrap formes 317→211

OCaml `add_fast` (plonk_curve_ops.ml:12) commence par
`let p1 = seal p1 in let p2 = seal p2 in`. Notre add_fast passait les
lincoms brutes au gate EC. Effet mesuré: `c0c00` 55→**0** (forme parasite
éliminée), `cc000` 83→138 vs jsoo 136 (quasi aligné, +2).
⚠ differingRows N'A PAS bougé (8992) — normal: c'est un fix de FORME; le
câblage reste décalé tant que des écarts amont subsistent. Toujours
regarder les DEUX métriques (cf. section «Deux métriques, deux axes»).

## RÈGLE GÉNÉRALE qui se dégage (4 fixes, même nature)

Les conventions d'écriture littérales d'OCaml sont STRUCTURELLES pour la
VK, alors qu'elles ne changent aucune valeur:
 1. `Boolean::all` → `equal (const n) sum` (constante à GAUCHE)
 2. `challenge_polynomial` → `f i * !r` (nouveau facteur à GAUCHE)
 3. `add_fast` → `seal` des entrées AVANT le gate
 4. opt-sponge wrap → skip réel, jamais d'absorb de zéros
⇒ Quand une forme diverge, LIRE LE LITTÉRAL OCaml (ordre des opérandes,
seal, lazy) — pas la sémantique. L'histogramme de signatures rend ces
conventions visibles; c'est l'outil n°1.

ÉTAT (tout pushé, recorded 21/21, init=0):
 init  differingRows 0 ✅
 update  +39 net / 8345 rows / 123 formes
 merge   +79 net / 15885 rows / (formes non mesurées)
 wrap    +26 net / 8992 rows / **211 formes** (était 689)
FILONS WRAP restants (diffus, plus de gros couple): `c1c0c` +36 vs
`11c0c` −14 (diff = 1er coeff c vs 1 → opérande scalée vs nue; 24 rows
dans «finalize unfinalized» non sous-labellisé, 7 ft_eval0, 5 env),
`ccc00` +32, `00c10` −26, `001c0` +23, `11c00` +18.
PROCHAIN PAS SUGGÉRÉ: sous-labelliser le reste de wrap_main «finalize
unfinalized» (24 rows anonymes) comme on l'a fait pour fr-sponge/sg_evals,
puis traiter `c1c0c`/`11c0c`.

## 🔑 STRATÉGIE RÉVISÉE — viser runDiffs AVANT les formes

Constat mesuré (wrap): differingRows=8992 mais seulement 211 écarts de
FORME ⇒ ~8800 lignes ne diffèrent QUE par le CÂBLAGE. Or le câblage
cascade: une seule ligne insérée/supprimée en amont décale tout l'aval et
fait diverger tous les wires suivants. ⇒ Corriger les formes NE FERA PAS
tomber differingRows tant que le PLACEMENT diffère.

ORDRE DE BATAILLE correct:
 1. **runDiffs → 0** (anchor-walk: longueurs des runs Generic entre ancres
    non-Generic). Actuel: update 42 (net +39), merge 224 (+79),
    wrap 197 (+26). C'est LA métrique à écraser d'abord.
 2. Puis les formes résiduelles (sig histogram).
 3. differingRows tombera alors en grande partie tout seul; le reste sera
    du vrai désaccord de wiring (permutation/copy-constraints).
init=0 valide toute la chaîne: quand placement+formes sont bons, le
câblage suit et la VK matche.

## SOUS-LABELS finalize (fait) — pour attribuer les poches

Ajoutés (aucun impact circuit, pur debug): `| sg_evals`, `| fr-sponge`,
`| b_actual`, `| b check`, `| cip check`, `| perm check`, `| zetaw`,
`| domain_for_compiled` (+ ceux déjà là: env, linearization, ft_eval0,
perm scalar, cip fold[ masked], dead pow chains, xi/r/bp-challenge
to_field). RESTE ~16 lignes en `wrap_main: finalize unfinalized` nu →
sous-labelliser les derniers sites si besoin.
Attribution actuelle de `c1c0c` (+36, forme `[c,1,c,0,c]` vs jsoo
`[1,1,c,0,c]` — 1er coeff scalé vs nu, donc encore un seal/opérande
matérialisé manquant): 16 nu, 7 ft_eval0, 5 env, 5 verify step proof,
4 cip check, 4 b check. Diffus ⇒ traiter APRÈS runDiffs.

## ÉTAT FIN SESSION 3 — reprise ici

Tout pushé sur `pickle-rs`, recorded 21/21 à chaque commit, **init
differingRows=0** (byte-identique) en permanence.

MESURES ACTUELLES (après les 5 fixes ci-dessous):
  init    runDiffs 0    net +0    differingRows 0 ✅
  update  runDiffs 42   net +37   8613   formes 123
  merge   runDiffs 224  net +73   17952
  wrap    runDiffs 197  net +26   8992   formes 211 (était 689)

⚠ differingRows n'est PAS une métrique de progrès tant que le placement
diverge: retirer/ajouter 1 ligne décale tout l'aval et désaligne la
comparaison index-par-index (le fix step_main a amélioré netGeneric
+39→+37 mais fait monter differingRows 8345→8613). Suivre **runDiffs +
netGeneric** d'abord; differingRows ne devient lisible qu'une fois le
placement exact.

FIXES LANDÉS SESSION 3 (tous = conventions littérales OCaml, aucune
valeur changée, toutes structurelles pour la VK):
 1. `Boolean::all` → `equal (const n) sum` (constante à gauche). -64
    gadgets de forme.
 2. `challenge_polynomial` → `f i * !r` (facteur neuf à GAUCHE).
 3. **opt-sponge wrap** (4 maillons: prover trim / oracles / circuit
    opt-absorb / **wrap_witness skip**). wrap formes 689→317, rows
    11158→8992 à ce moment-là.
 4. `add_fast` → `seal` des 2 points (plonk_curve_ops.ml:12). formes
    317→211, `c0c00` 55→0.
 5. `step_main` → ok = `verified &&& finalized ||| not must_verify` (1
    and + 1 or, PAS d'assert par proof) + `Boolean.Assert.all` =
    `assert_equal (sum bs) (const n)`. net −2/proof seulement.

PROCHAIN PAS — les 3 plus gros runDiffs, dans l'ordre:
 • **update @6645 (+24)** et merge @6646/@13284 (+23 chacun): fenêtre
   entre [CompleteAdd][CompleteAdd] et [Poseidon], 30 lignes chez nous vs
   6 chez jsoo. Motif RÉPÉTITIF xor/mul/`-1-00` → ressemble à un
   consume_pairs d'opt-sponge. Labels = `recursive_step.rs:4943` = le loc
   NU de step_main, MAIS ce loc est aussi transmis à verify_one ⇒ ces
   lignes viennent probablement de la QUEUE de verify_one (candidat:
   `hash_messages_for_next_step_proof_opt`, l'ANCIEN digest opt-sponge,
   ou la ré-émission de la sponge d'index). ACTION: sous-labelliser
   verify_one (step_verifier.rs) phase par phase — c'est ce qui a
   débloqué @892 et le wrap. NE PAS deviner: labelliser puis mesurer.
 • **wrap @2354 (+53)**: ancre CompleteAdd, j226/r279.
 • wrap @2046 (−10), @0 (−8); update @764 (+8), @892 (+7), @6 (−4).

## CIBLE N°1 CARACTÉRISÉE — update @6645 (+24), merge @6646/@13284

Sous-labels ajoutés cette session (impact circuit NUL, gardés):
step_verifier: `| index sponge`, `| old digest[ opt]`, `| alpha/zeta
to_field`, `| finalize`, `| verify wrap proof`, `| should_finalize==
must_verify`; step_main: `| new index sponge`, `| new digest`,
`| Assert.all oks`; incrementally_verify: `| multiscale_known`,
`| absorb x_hat`, `| absorb w_comm`, `| absorb z_comm`,
`| absorb vk_digest`; finalize: `| sg_evals`, `| fr-sponge`, `| b_actual`,
`| b check`, `| cip check`, `| perm check`, `| zetaw`,
`| domain_for_compiled`.

ATTRIBUTION @6645: les 28 lignes tombent dans **`| verify wrap proof`**
(donc dans incrementally_verify_proof) mais AUCUN des sous-labels ajoutés
ne les capte ⇒ elles viennent d'un site encore à loc nu dans
incrementally_verify.rs (candidats restants: squeeze beta/gamma/alpha via
`lowest_128_bits` l.377-389, absorb t_comm, ft_comm, combine_commitments,
bulletproof/ipa_challenges_transcript).

CONTEXTE EXACT (mesuré):
  ancres: @6641 VarBaseMul, @6642 VarBaseMul, @6643 CompleteAdd(run 1),
          @6644 CompleteAdd(run 3), @6645 **Poseidon** (train = une
          permutation de sponge)
  jsoo run=6, rust run=30.
  Les 5 PREMIÈRES lignes sont IDENTIQUES à jsoo:
    00010|1--00, -0-01|1--00, 1--00|001-0, 1--00|00010, 001-0|-0-01
  jsoo s'arrête à la 6e (001-0|001-0). Nous enchaînons 24 lignes d'un
  MOTIF RÉPÉTITIF: 1--00|001-0, 001-0|-1-00, -1-00|1--00, … (reduce de
  lincom 2-termes + mul, en boucle ~8×).
⇒ Lecture: on fait la même chose que jsoo puis on exécute une BOUCLE que
jsoo n'a pas (ou qu'il fait hors-circuit / replie). `1--00`=[1,-,-,0,0]=
reduce `x−y`; `001-0`=mul. Chercher une boucle de ~8 itérations
(mul+reduce) juste avant une absorption de sponge, après un scale_fast
(VarBaseMul) + add_fast (CompleteAdd). PISTE: b_poly/challenge_polynomial
recalculé en circuit là où OCaml passe une valeur déjà connue, ou
`lowest_128_bits`/squeeze qui reconstruit des bits.
ACTION SUIVANTE: labelliser les sites restants d'incrementally_verify.rs
(l.377-389 squeeze/lowest_128_bits, t_comm, ft_comm, combine, bulletproof)
puis re-mesurer. NE PAS deviner — chaque cycle = ~4 min de rebuild natif,
donc labelliser LARGE d'un coup.

### @6645 — FENÊTRE BORNÉE (astuce: lire les labels des ANCRES)

Pas besoin de rebuild pour localiser: les ancres non-Generic PORTENT un
label. Les lire encadre la fenêtre immédiatement:
  @6640-6642 VarBaseMul  "scale_fast | … | verify wrap proof"
  @6643 CompleteAdd      "… | scale_fast2 h_minus_g add"
  @6644 CompleteAdd      "… | **bulletproof rhs add**"   ← borne gauche
  … 30 lignes (rust) / 6 (jsoo) …
  @6645+ Poseidon        "… | **new index sponge**"      ← borne droite
⇒ Les 28 lignes sont la QUEUE de `verify()` (step_verifier.rs), entre la
fin du bulletproof et le nouveau digest de step_main. Contenu attendu:
`check_bulletproof_equation_from_q` (equal_g), le bypass base-case des 16
bulletproof challenges (`sys.if_`), les 4 asserts plonk.
VÉRIFIÉ: OCaml (step_verifier.ml:1305-1316) fait la MÊME chose — 16 ×
(`Field.if_ is_base_case ~then_:c1 ~else_:c2` + `Field.Assert.equal c1
c2`); et `Assert.equal` entre 2 vars de même scale n'émet AUCUN gate
(union-find, plonk_constraint_system.ml Equal case) — idem chez nous.
⇒ Le surplus n'est PAS le bypass. Reste à instrumenter: le `equal_g`
(check_bulletproof_equation_from_q) et `ft_comm` (incrementally_verify.rs
l.426, encore à loc nu), + l.539 (absorb delta), 349/373/374
(public_input_commitment), 304-309 (index sponge), 335 (sg_old absorb).
ASTUCE À RÉUTILISER: labels des ancres = localisation gratuite, sans
rebuild. Toujours commencer par là.

## ✅ FIX must_verify constant — le plus gros gain update/merge

CAUSE: OCaml prend `must_verify` de la RÈGLE (`proof_must_verify`,
inductive_rule.ml) = constante `Boolean.true_` pour un slot réellement
vérifié. Nous le prenions du STATEMENT (`should_finalize`, une variable).
EFFET EN CASCADE du littéral OCaml: `not must_verify` devient la constante
false ⇒ les 16 `Field.if_ is_base_case` (bypass des bulletproof
challenges) ET le `||| not must_verify` du résultat par proof se REPLIENT
sans aucun gate. jsoo: 6 lignes dans cette queue; nous: 30.
SÛRETÉ: `verify_one` assertit toujours `should_finalize == must_verify`
(step_main.ml:28) ⇒ le slot du statement est épinglé à 1, rien n'est
perdu. Les slots dummy ne passent jamais par verify_one.

MESURES: update net **+37→+6**, rows 8613→**7296**; merge net **+73→+13**,
rows 17952→**15309**; @6645 DISPARU; init reste 0; wrap inchangé.

⇒ RÈGLE ÉTENDUE: les conventions littérales d'OCaml incluent **D'OÙ VIENT
UNE INFO**. Ce qu'OCaml connaît statiquement (règle, feature flags,
largeurs) doit être une CONSTANTE chez nous — sinon les gadgets ne se
replient pas et le circuit diverge. CHERCHER D'AUTRES CAS: tout
`sys.compute(|_| <valeur connue à la compilation>)` est suspect.

NB: runDiffs est MONTÉ (update 42→111) pendant que le net s'effondrait:
le placement s'est redistribué en beaucoup de petits ±1 au lieu de
quelques gros écarts. C'est normal et plutôt bon signe (on approche), mais
la suite sera de la dentelle, plus des gros leviers.

## 🔎 LIRE LA DISTRIBUTION DES runDiffs (pas seulement le compte)

Distribution mesurée après le fix must_verify:
  update: 111 runDiffs = **54×(+1) + 54×(−1)** + @764(+8) + @6(−4) + @892(+2)
  merge:  121 runDiffs = **59×(+1) + 57×(−1)** + @765(+9) + @7403(+8) + @6(−4) + @7(−4)
  wrap:   196 runDiffs = **89×(+1) + 88×(−1)** + @2354(+53) + @2046(−10) + @0(−8) + @1694(+5)

Les ±1 sont APPARIÉS ⇒ artefact de PACKING (un gate Generic porte 2
gadgets; un gadget qui bascule dans l'autre demi-ligne décale une
frontière d'ancre de 1: +1 ici, −1 là, net nul). Ils NE sont PAS des
lignes en trop et se résorberont quand le flux de gadgets sera exact.
⇒ Un runDiffs élevé n'est pas alarmant en soi: soustraire les paires ±1
pour voir les VRAIS écarts. update n'a plus que **3 vrais écarts**.

CIBLES RÉELLES RESTANTES (ordre de taille):
 1. **wrap @2354 (+53)** — ancre CompleteAdd, j226/r279. LE plus gros.
 2. merge @765 (+9) / @7403 (+8) ; update @764 (+8) — même région
    (finalize, cf. la chaîne zeta_to_srs 16 muls + résidus).
 3. wrap @2046 (−10), @0 (−8) ; update/merge @6 (−4), merge @7 (−4).
 4. update @892 (+2), wrap @1694 (+5).
MÉTHODE: labels des ANCRES d'abord (gratuit, sans rebuild) pour borner la
fenêtre, PUIS labels par-op si besoin.

## ⚠ statement_terms seal — HYPOTHÈSE RÉFUTÉE PAR LA MESURE

J'ai cru (session 3) que le `seal` des sommes lagrange one-hot
(public_input.rs::statement_terms) était un ajout abusif d'une session
antérieure, au motif qu'OCaml `lagrange` (wrap_verifier.ml:334-356) finit
par `Vector.reduce_exn ~f:(… Field.( + ))` — une SOMME de lincoms SANS
seal. J'ai retiré le seal ⇒ **le wrap a EMPIRÉ**: netGeneric +26→**+84**,
differingRows 8992→9856 (+58 lignes). REVERTÉ.
RAISON: sans seal, la lincom est RE-MATÉRIALISÉE à chaque usage par nos
consommateurs (c'était déjà noté session 2: "lazy hetero lagranges made
wrap Generic WORSE 3639 vs 3581"). OCaml ne scelle pas MAIS son pattern de
CONSOMMATION diffère (chaque terme est réduit une seule fois par son
consommateur). Le seal compense chez nous.
⇒ Pour vraiment matcher: il faudrait aligner AUSSI la façon dont les
termes lagrange sont consommés (x_hat/MSM), pas juste le seal. Tant que ce
n'est pas fait, GARDER le seal (approximation la plus proche).
⇒ LEÇON: le littéral OCaml est le juge, mais un fragment isolé ne suffit
pas — il faut le littéral DU CONTEXTE COMPLET (production ET
consommation). Et TOUJOURS mesurer avant de conclure: mon raisonnement
"OCaml ne scelle pas donc on ne doit pas sceller" était plausible et FAUX.
Le +53 de wrap @2354 reste donc OUVERT (cause: pattern de consommation).

## ⚠ PIÈGE LABELLING — replace(a,b,1) ne touche que la 1re occurrence

3 cycles de rebuild perdus: `public_input_commitment` apparaît 2× (chemin
MultiscaleKnown du step l.349, chemin Statement du wrap l.373-374). Mes
sed/replace en `count=1` n'ont labellisé que le premier, donc le wrap
restait anonyme alors que je le croyais couvert. Vérifier le NOMBRE
d'occurrences avant de remplacer.

## ✅ FIX Cond_add sans correction — wrap +26 → +2

CAUSE: OCaml a DEUX constructeurs de terme (wrap_verifier.ml:911-922):
  | b, 1 -> `Cond_add (b, lagrange …)             ← PAS de correction
  | x, n -> `Add_with_correction ((x,n), lagrange_with_correction …)
Notre `next()` sélectionnait ET scellait TOUJOURS les 2 points, puis les
arms Cond jetaient la correction (`let (lagrange, _) = next(...)`). Chaque
élément de champ se décompose en [Packed(255), Cond(bit)] ⇒ ~15-20
corrections payées pour rien = les +53 de wrap @2354.
FIX: `next(sys, &mut slot, want_correction) -> (Point, Option<Point>)`.
MESURE: wrap net **+26→+2** (Generic 3214 vs 3216 !), rows 8992→**8654**.

## 📊 ÉTAT — le chantier PLACEMENT est quasi fini

  init    net **0**   rows **0**     ✅ byte-identique
  update  net **+6**  rows 7296
  merge   net **+13** rows 15309
  wrap    net **+2**  rows 8654
Les 4 circuits sont à quelques lignes du volume jsoo. Les runDiffs
restants sont majoritairement des paires ±1 (packing).

## 🧭 INFLEXION DE MÉTHODE (ce qui marche le mieux en fin de parcours)

Les 6 premiers fixes venaient des OUTILS (histogramme de signatures,
anchor-walk) qui POINTENT l'anomalie. Les 2 derniers (`must_verify`
constant, `Cond_add` sans correction) viennent d'une lecture STRUCTURELLE
du littéral: comparer les TYPES/CONSTRUCTEURS d'OCaml, pas les gates.
`Cond_add` vs `Add_with_correction` = 2 constructeurs distincts: la
divergence était dans le TYPE, invisible au niveau gate.
⇒ En fin de parcours, lire les types de données OCaml (Spec.pack, les
variants) est plus rentable que traquer les gadgets.
INDICE UTILE: un `let (x, _) = f(...)` qui jette une valeur coûteuse est
un signal fort (on paie une construction qu'OCaml ne fait pas).

## 🔑 RÈGLE NEUVE — OCaml évalue les `cons` DROITE-À-GAUCHE

C'est une convention D'ÉMISSION, invisible en lisant `f` seule. Dans
`plonkish_prelude/vector.ml` :

  init : `f i :: init (i + 1) n ~f`   (l.124) → cons ⇒ **f court DÉCROISSANT**
  map  : `f x :: map xs ~f`           (l.141) → cons ⇒ **f court DÉCROISSANT**
  map2 : `f x y :: map2 xs ys ~f`     (l.69)  → cons ⇒ **DÉCROISSANT**
  iter : `f x ; iter xs ~f`           (l.21)  → `;` séquencé ⇒ **CROISSANT**
  fold : accumulateur explicite               ⇒ **CROISSANT**

OCaml n'ordonne pas l'évaluation des arguments de constructeur ; ocamlc/
ocamlopt (donc jsoo) évaluent DE DROITE À GAUCHE ⇒ la queue récursive est
évaluée AVANT `f i`. Donc tout `Vector.map`/`init` dont `f` ÉMET DES
CONTRAINTES les émet À L'ENVERS. `Vector.iter` non.

⚠ MAIS (mesuré) : l'inversion n'est OBSERVABLE que si les blocs produits
par `f` DIFFÈRENT entre eux ou PARTAGENT des variables. Inverser N blocs
AUTONOMES et de forme IDENTIQUE rend un circuit identique — voir le
no-op n°2 ci-dessous. Toujours se demander « les blocs sont-ils
distinguables ? » AVANT d'implémenter.

## ✅ FIX (commit f915511c01) — deux conventions d'ordre d'émission

1. **`Checked.assert_all` émet la liste À L'ENVERS** (checked.ml:75) :
   `List.fold_right cs ~init ~f:(fun c acc -> bind acc (fun () -> add c))`
   construit `f c0 (f c1 init)` ⇒ exécution = init, c1, c0.
   Donc `equal_constraints` (utils.ml:43) émet `r1cs r z 0` AVANT
   `r1cs z_inv z (1-r)`. STRUCTUREL : `z` est une lincom non réduite, le
   PREMIER r1cs porte ses gadgets de réduction.
   INDICE qui a mis sur la piste : `api.rs::other_field_equal` ET
   `bulletproof.rs` réimplémentaient DÉJÀ `equal` à la main avec
   l'inversion (+ commentaire) — deux contournements locaux d'un bug
   jamais remonté dans le `FieldVar::equal` générique de `cvar.rs`.
2. **`One_hot_vector.of_index`** = `Vector.init length ~f:(fun j ->
   Field.equal (Field.of_int j) i)` ⇒ bits créés j = length-1 → 0.
   Comme `reduce_lincom` trie par INDEX DE VARIABLE CROISSANT, l'ordre de
   CRÉATION décide quel poids de branche atterrit en slot `l` vs `r`.
MESURE : à `api.rs:630` le flux de gadgets colle à jsoo position par
position et les lignes 81-82 sont BYTE-IDENTIQUES (coeffs `[1,2,...]`,
wires égaux). wrap differingRows 8654→**8640**. init reste 0, recorded 21/21.

## 🛠 OUTIL DÉCISIF — dumper les COEFFICIENTS RÉELS + WIRES

`scratchpad/rawcoeff.mjs`. L'histogramme à 4 symboles (`0/1/-/c`) écrase
tout constante en `c` et CACHE l'info. Voir les valeurs littérales
`B[1, 2, -c, 0, 0]` (jsoo) vs `B[2, 1, -c, 0, 0]` (rust) AVEC des wires
IDENTIQUES a immédiatement identifié les coeffs comme les largeurs de
branches et réduit le problème à un ordre de création. Le symbole disait
seulement `1cc00` vs `c1c00` = « l/r inversés », sans dire pourquoi.
⇒ Quand une forme diverge, dumper les VALEURS avant de théoriser.
Autres outils ajoutés : `head_dump.mjs`, `gstream.mjs` (diff LCS du FLUX
DE GADGETS — Generic empile 2 gadgets/ligne, la compa ligne-à-ligne ment),
`anchor_row.mjs` (index d'ancre → ligne + labels du run).

## ❌ DEUX NO-OPS RÉFUTÉS PAR LA MESURE — NE PAS REFAIRE

1. **Renverser `to_constant_and_terms`** (cvar.rs). OCaml (cvar.ml:54)
   fait `(scale, v) :: terms` ⇒ sa liste de termes sort INVERSÉE vs notre
   `terms.push(...)`. Lecture juste, effet **NUL** : le consommateur
   `reduce_lincom` fait `accumulate_terms(terms)` → une MAP indexée par
   variable, puis `Map.fold_right` ⇒ ordre d'entrée DÉTRUIT, ressorti en
   index croissant. L'ordre de la liste ne peut pas compter.
2. **Renverser les 16 `bp-challenge to_field`** (finalize.rs, iso
   `compute_challenges` = `Vector.map`). Effet **NUL au bit près** (label
   pourtant présent : 256/128/240 lignes, build vérifié frais). CAUSE :
   `scalar_to_field` témoigne tout en interne ⇒ les 16 blocs sont
   AUTONOMES et de forme IDENTIQUE ; permuter des blocs autonomes
   identiques rend un circuit identique, wires compris. Invisible PAR
   CONSTRUCTION, donc définitivement — pas « pas encore ».

## 🧭 LEÇON DE MÉTHODE (répétition de l'épisode `seal`)

J'ai RE-commis l'erreur documentée en §« statement_terms seal » : conclure
d'un fragment de littéral OCaml isolé sans vérifier le CONSOMMATEUR. Les
deux no-ops ci-dessus en découlent directement.
⇒ PROTOCOLE : avant d'implémenter une correction d'ordre de PRODUCTION,
répondre à « qui consomme cet ordre, et le préserve-t-il ? ». Ici :
`accumulate_terms` l'écrase (no-op 1) ; des blocs autonomes le rendent
inobservable (no-op 2).
⇒ Et poser une PRÉDICTION FALSIFIABLE avant de mesurer. Pour le fix
one-hot : « les coeffs à api.rs:630 doivent passer de (2,1) à (1,2) ».
Elle a tenu ⇒ la chaîne production→consommation était comprise. Sans
prédiction, une mesure qui bouge peu est ininterprétable.

## 📊 ÉTAT AU 2026-07-17 (fin de session 4) — reprise ici

  init    runDiffs 0    net  +0   differingRows **0** ✅ byte-identique
  update  runDiffs 111  net  +6   7296
  merge   runDiffs 121  net +13   15309
  wrap    runDiffs 197  net  +2   **8640**
Tout pushé sur `pickle-rs` (HEAD f915511c01), recorded 21/21.
Le PLACEMENT est quasi fini (net +0/+6/+13/+2) ; l'essentiel des
differingRows est du CÂBLAGE, qui cascade tant que le placement diverge.

PROCHAINES CIBLES (résidus runDiffs, par ordre d'intérêt) :
 • **wrap @0 (−8)** : j167/r159, tout début du circuit ⇒ AUCUNE dérive
   amont possible, la cible la plus propre. Les lignes 0-72 sont déjà
   identiques ; la divergence commence à la ligne 73 (`api.rs:488/495` =
   `other_field_equal`) où un bloc est RÉORDONNÉ, puis les lignes 81-85
   sont désormais bonnes. ⇒ reprendre par `gstream.mjs wrap 68 100`.
 • update @6 / merge @6/@7 (−4 chacun) : run `recursive_step.rs:4420`.
   Le MÊME −4 sur 3 circuits ⇒ une seule cause partagée.
 • update @764 (+8) / merge @765 (+9) : noyés dans le run `finalize |
   linearization` (680 lignes) ⇒ sous-labelliser avant d'attaquer.
 • wrap @847 (+4), @727/@1574 (+2).
PISTE TRANSVERSE : rejouer la règle « cons droite-à-gauche » sur les
`Vector.map` in-circuit dont les blocs sont DISTINGUABLES (pas autonomes /
formes différentes) — candidats : `step_verifier.ml:902`,
`wrap_verifier.ml:1542` (`Vector.map old_bulletproof_challenges`),
`step_verifier.ml:1203` (`Vector.map2 proofs_verified_mask ...` — masqué
donc les blocs DIFFÈRENT ⇒ le meilleur candidat), `wrap_verifier.ml:63`
et `:338/:362/:430` (`Vector.map domains`).

## 🐞 BUG D'OUTILLAGE CORRIGÉ — le wrap était décodé dans le MAUVAIS CORPS

Les scripts décodaient TOUS les circuits avec le module **Fp** (Pallas
scalar). Or le WRAP est sur **Fq** (Vesta scalar). Conséquence : le vrai
`-1` de Fq (= Fq−1) ne tombait pas sur `Fp−1` et sortait donc en `c`
« constante quelconque » au lieu de `-`.
⇒ Les gadgets du wrap paraissaient exotiques (`1cc00`, `c0010`) alors
qu'ils sont banals : `1c-00` = `1·w0 + c·w1 − res = 0` (réduction de
lincom), `-0010` = `b·(b−1) = 0` (**check booléen**), `11-00` = somme.
⇒ Le DIFF restait valide (même décodage des 2 côtés), mais la LECTURE
était faussée et le chiffre « wrap formes 211 » des notes antérieures est
calculé avec le mauvais module (les BUCKETS sont faux, pas le diff).
FIX : `FP_MODULUS`/`FQ_MODULUS` + sélection par circuit dans
`gstream.mjs`, `head_dump.mjs`, `rawcoeff.mjs` (`measure.mjs` n'utilise
que les TYPES de gates, pas de module).
LEÇON : un outil de mesure a aussi besoin d'être vérifié. Un symbole
`c` inattendu et récurrent = suspecter le décodeur AVANT la théorie.

## 🎯 TÊTE DU WRAP — désormais BYTE-IDENTIQUE jusqu'à la ligne 89

Le fix one-hot a fait bien plus que ses −12 lignes agrégées : le bloc
RÉORDONNÉ des lignes 73-79 (`other_field_equal`) a disparu AVEC lui —
même cause racine (l'ordre d'émission de la boucle de branches). Avant :
identique jusqu'à 72. Après : **identique jusqu'à 89**.
⇒ Rappel : `differingRows` agrégé SOUS-ESTIME les vrais progrès de tête.
Vérifier avec `gstream.mjs` où la 1re divergence tombe VRAIMENT.

## 🔎 CIBLE N°1 SUIVANTE — wrap r90, +1 ligne, checks booléens INLINE

1re divergence du wrap = `r90` : rust émet 2 gadgets `-0010`
(= `b·(b−1)=0`) de plus, labels `api.rs:699` (`should_finalize`) et
`api.rs:759` (slot Bool du statement).
COMPTE GLOBAL wrap : jsoo **82** checks booléens, rust **74** (−8) — et
`wrap @0` vaut exactement **−8**. Sites rust : 55 `x_hat commitment`,
12 `statement_terms`, 3 `group_map u`, 2 `:699`, 2 `:759`.
HYPOTHÈSE (à VÉRIFIER avant d'implémenter, cf. protocole) : OCaml
`exists typ` ALLOUE TOUS LES CHAMPS PUIS lance `typ.check` sur la
structure entière ⇒ les checks booléens arrivent APRÈS toutes les
allocations. Nous témoignons+checkons EN LIGNE, champ par champ. Pire,
notre `api.rs:698` calcule `should_finalize` AVANT alpha/beta/… alors
que c'est le DERNIER champ du record OCaml.
⇒ Lire `Typ`/`exists` dans snarky (`typ.var_of_fields` puis `typ.check`)
et l'ordre des champs de `Types.Step.Proof_state`. PRÉDICTION à poser
avant mesure : la ligne `r90` doit disparaître et les 2 checks
réapparaître plus loin, groupés.

## ❌ NO-OP N°3 RÉFUTÉ — « exists alloue-tout-puis-checke » (INVISIBLE)

TESTÉ : réordonner le témoignage de `unf_deferred` dans l'ordre `to_data`
d'OCaml (should_finalize EN DERNIER) + différer les checks booléens après
toutes les allocations, iso `checked_runner.ml:219-226`.
RÉSULTAT : **nul au bit près** (8640/7296/15309 inchangés), et la ligne
`r90` excédentaire est TOUJOURS là (label bien déplacé 699→752 ⇒ le code
s'exécutait). Reverté.

**LA RAISON — À RETENIR ABSOLUMENT :**
**TÉMOIGNER N'ÉMET AUCUNE GATE.** `exists`/`compute` = `store_field_elt`,
zéro contrainte. Donc « allouer-tout-puis-checker » vs « entrelacer »
donnent EXACTEMENT la même séquence de gates. L'ordre d'un `exists` ne
peut agir QUE via les INDEX DE VARIABLES (que `reduce_lincom` trie en
croissant) — et ici ces variables ne retombent sur aucune lincom
multi-termes triée ⇒ invisible.
⇒ COROLLAIRE GÉNÉRAL : ne JAMAIS attendre d'un réordonnancement de
témoins qu'il déplace des lignes. Il ne déplace que des index. Ne le
tenter que si l'on peut nommer la lincom en aval dont le tri changera.
⇒ Ça invalide la « CIBLE N°1 » de la section précédente : le `+2` de
`r90` n'est PAS un problème d'ordre.

## 🔎 CIBLE N°1 RÉVISÉE — wrap r90 : 2 checks booléens VRAIMENT en trop

FAITS ÉTABLIS (pas des hypothèses) :
 • Tête du wrap BYTE-IDENTIQUE jusqu'à la ligne **89**. 1re divergence =
   `r90`, +1 ligne, 2 gadgets `-0010` (`b·(b−1)=0`) labels `api.rs:699`
   (`should_finalize`) et `:759` (slot Bool du statement).
 • Compte GLOBAL wrap : jsoo **82** checks booléens, rust **74** (−8).
   Donc rust en a 2 de TROP ici mais 8 de MOINS au total.
 • jsoo CHECKE bien `should_finalize` : `Spec` mappe `Bool -> Boolean.typ`
   (spec.ml:522 step / :566 wrap) ⇒ ce n'est PAS « on checke, eux non ».
 • Sites rust des 74 : 55 `x_hat commitment`, 12 `statement_terms`,
   3 `group_map u`, 2 `:699`, 2 `:759`.
PROCHAIN PAS : localiser les 82 de jsoo par ligne et diffuser le compte
par ZONE (pas par label, qu'on n'a pas côté jsoo) : découper les 2
circuits en tranches entre ancres communes et comparer le nombre de
`-0010` par tranche. La tranche où jsoo en a ~10 de plus dira où l'on
oublie des checks — CHERCHER LES CHECKS MANQUANTS d'abord (−8 global),
le `+2` local en est probablement le pendant (des checks émis au mauvais
endroit, pas en trop). Candidat : `x_hat commitment` (55 chez nous) et
les bits de `Spec.pack`/`Packed_bits` du statement.

## 🎯 LES 8 CHECKS MANQUANTS — LOCALISÉS EXACTEMENT (outil `boolslice.mjs`)

MÉTHODE (nouvel outil `scratchpad/boolslice.mjs`) : découper les 2
circuits en TRANCHES entre ancres communes et compter les gadgets
`-0010` (`b·(b−1)=0`) par tranche. Contourne le fait qu'on n'a pas de
labels côté jsoo. Sur tout le wrap, SEULES 2 tranches diffèrent :

  ancres    0..100   lignes j0-401     r0-394     jsoo  2  rust  4   **+2**
  ancres 2000..2100  lignes j4186-4439 r4193-4436 jsoo 10  rust  0   **−10**
  (total jsoo 82 / rust 74 ⇒ net −8 ✓ cohérent)

**LA ZONE −10 EST UN MOTIF PARFAITEMENT RECONNAISSABLE.** jsoo, lignes
**4368-4377**, DIX lignes consécutives portant chacune :
  A = `[-1, 0, 0, 1, 0]`  = `b·(b−1) = 0`      (check booléen)
  B = `[ 2, 1, -1, 0, 0]` = `2·acc + bit − res = 0`  (accumulation)
… puis **[Poseidon] en 4378-4379**. C'est un **pack bits→field MSB-first
sur 10 BITS**, chaque bit contraint booléen, juste avant une absorption
Poseidon. Nous n'émettons RIEN là (on est encore dans `assert_on_curve`,
label `api.rs:446`, 228 lignes dans la fenêtre).

PISTE FORTE : c'est la signature de **`Spec.pack` / `Packed_bits`**
(spec.ml:145 `p.pack Bool …`, spec.ml:227 `Bool -> Packed_bits (x, 1)`,
`Digest -> Packed_bits (x, size_in_bits)`) — le wrap SÉRIALISE le
statement du step en bits avant de l'absorber dans la sponge, et nous
passons probablement les valeurs DIRECTEMENT sans repasser par les bits.
10 bits = très probablement **`Branch_data`** = `proofs_verified_mask`
(2 bits) + `domain_log2` (8 bits) — cf. `Branch_data.Checked.pack` =
`domain_log2·4 + mask`, et `branch_data.ml:135` `typ ~assert_16_bits`.
⇒ PROCHAIN PAS : lire `Spec.pack`/`Spec.wrap_typ` et le chemin
`messages_for_next_wrap_proof` / absorption du statement dans wrap_main,
identifier QUEL champ fait 10 bits, et voir pourquoi notre port
court-circuite l'unpack. PRÉDICTION à poser : la tranche ancres
2000..2100 doit passer de 0 à 10 checks et le compte global à 82/82.
⚠ Ce sont bien des GATES (pas des témoins) ⇒ contrairement au no-op n°3,
ce fix DOIT déplacer des lignes. C'est donc mesurable.

## ✅ LES 10 BITS SONT IDENTIFIÉS — `Branch_data` (littéral confirmé)

CHAÎNE COMPLÈTE, tout vérifié dans le littéral (aucune supposition) :
 • `branch_data.ml:58` : **`let length_in_bits = 10`** ⇒ les 10 checks
   booléens de jsoo (wrap 4368-4377) sont l'unpack de **Branch_data**.
 • `spec.ml:236` : `| Branch_data -> [| `Packed_bits
   (Branch_data_checked.pack x, Branch_data.length_in_bits) |]`
   (rappel: `Bool -> Packed_bits (x,1)`, `Digest -> Packed_bits (x,255)`,
   `Challenge`/`Bulletproof_challenge -> Packed_bits (x, 128)`).
 • CONSOMMATEUR = `wrap_main.ml:486-493` :
     `~public_input:(Array.map (pack_statement Max_proofs_verified.n
        prev_statement) ~f:(function
          | `Field (Shifted_value x) -> `Field (split_field x)
          | `Packed_bits (x, n) -> `Packed_bits (x, n)))`
   passé à `Wrap_verifier.incrementally_verify_proof`.
 ⇒ C'est le chemin **x_hat / public_input**, donc NOTRE `public_input.rs`
   (celui du fix `Cond_add`), PAS un hash — le Poseidon de 4378 est la
   sponge qui suit.
 • Côté rust le slot existe déjà : `WrapStepStatementSlot::Packed
   { value, num_bits }` (api.rs:279), compté 1 élément, et
   `public_input.rs` en fait un `Add_with_correction ((x, n), …)`
   comme OCaml (wrap_verifier.ml:911-922).

**LA QUESTION PRÉCISE OÙ REPRENDRE** : le chemin `Add_with_correction
((x, n), …)` d'OCaml UNPACKE-T-IL `x` en `n` bits avec un check booléen
par bit ? Le motif observé chez jsoo est bien un unpack+repack :
  A = `b·(b−1)=0` (check) et B = `2·acc + bit − res` (recomposition)
… soit exactement `Field.unpack x ~length:10` puis repack — c'est-à-dire
une PREUVE QUE `x < 2^10`. Nous ne l'émettons PAS (0 check dans la
tranche).
⇒ LIRE : `Wrap_verifier.scale_fast` / `scale_fast2'` et le multiscale de
`incrementally_verify_proof` pour voir où les `n` bits d'un
`Packed_bits (x, n)` sont matérialisés, puis comparer à notre
`public_input.rs` + `plonk_curve_ops.rs`.
⇒ ATTENTION à la symétrie : la tranche de tête a `+2` (api.rs:699/759).
Il est probable que les DEUX anomalies soient le même bug : des bits
qu'on matérialise au mauvais endroit (2 en tête) et pas là où il faut
(10 dans le x_hat). Traiter les deux ensemble, pas séparément.
⇒ PRÉDICTION à poser : tranche ancres 2000..2100 de 0 → 10 checks,
tranche 0..100 de 4 → 2, total 82/82. C'est du GATE ⇒ mesurable.

## ✅✅ FIX VALIDÉ : les 10 checks = `split_field` × 10 à l'ÉVALUATION
## D'ARGUMENT — et l'hypothèse « Branch_data » ci-dessus est RÉFUTÉE

CORRECTION de l'entrée précédente : les 10 bits ne sont PAS Branch_data.
Le statement du STEP (celui que le wrap commit en x_hat) n'en contient
pas — son spec par proof (composition_types.ml:1213-1221) est :
  `[ Vector (B Field, 5); Vector (B Digest, 1); Vector (B Challenge, 2);
     Vector (Scalar Challenge, 3); Vector (B Bulletproof_challenge, 16);
     Vector (B Bool, 1) ]`
  fq = [cip; b; zeta_to_srs_length; zeta_to_domain_size; perm] (l.1245).
`Branch_data -> Packed_bits (x, 10)` (spec.ml:236) existe bien mais vit
dans le statement du WRAP consommé par le STEP (step_verifier), pas ici.
La chaîne littérale était vraie, le circuit visé était le mauvais.

CE QUE C'ÉTAIT VRAIMENT (prouvé par les WIRES jsoo, puis mesuré) :
**5 slots `Field` × 2 proofs = 10 `split_field`** émis par OCaml à
l'évaluation de `~public_input:(Array.map … split_field …)`
(wrap_main.ml:486-493) — c.-à-d. AU CALL de incrementally_verify_proof :
après les exists openings (:440) + messages (:470) (les on-curve), AVANT
le sponge « absorb verifier index ». `split_field` (wrap_main.ml:57-69) =
exists (field × Boolean.typ) [1 check bool] + `Assert.equal (2y+odd) x`
[1 gadget `[2,1,-1,0,0]`]. Preuve par wires (jsoo 4368-4377) :
  • bit de 4368A câblé dans le r du `[2,1,-1]` de 4369B (cycle
    4368.1→4369.4) — appariement décalé d'un ;
  • le x du split câblé vers la région finalize (o de 4369B → 1765.3) ;
  • le 10e linéaire DIFFÉRÉ à 4390B, apparié au 1er gadget generic de la
    région sponge — preuve de la file des demi-lignes.
La 2e anomalie (+2 en tête) : nos slots `Bool` du statement étaient
RE-témoignés (api.rs:759, compute → check Boolean.typ) alors qu'OCaml
REFILE les vars `should_finalize` de prev_proof_state (wrap_main.ml:
423-438) — pas de 2e check. Et wrap_verifier.ml:917 RE-asserte la
booléanité de chaque entrée (b,1) dans la boucle x_hat (odd bits inclus)
⇒ 12 checks x_hat (10 odd + 2 should_finalize), qu'on avait déjà.

RÈGLE STRUCTURELLE NEUVE (à réutiliser) :
**le csys kimchi apparie les gadgets Generic (NOUVEAU, PENDING)** —
plonk_constraint_system.ml:1452-1461 : `add_row [| l;r;o; l2;r2;o2 |]`
où (l2,r2,o2) est le PENDING ⇒ dans une ligne, le slot A est le gadget
émis en DERNIER, le slot B le plus ancien. Corollaire : la répartition
des gadgets dans les lignes dépend de la PARITÉ du nombre de gadgets
generic émis en amont (la « phase »). Un net amont ≠ 0 fait dériver la
phase de TOUT l'aval : les runs se re-découpent en paires ±1 autour des
ancres SANS différence de contenu. Signature mesurable : une queue de
runDiffs nombreux à NET 0 (aujourd'hui : 187 diffs net 0 sur ancres
2300+). NE PAS les chasser un par un — ils tomberont quand les nets
amont seront à 0.

LE FIX (commit courant, 3 éditions) :
 1. wrap_main.rs (après `witness_proof`) : expansion des
    `StepStatementElement::Split(x)` → `split_field` → `[Packed(y,255),
    Bool(odd)]` — à la position d'évaluation d'argument OCaml.
 2. public_input.rs `statement_terms` : branche `Split` → unreachable!
    (l'expansion est en amont) ; la branche `Bool` fait le re-assert
    :917 pour odd bits ET should_finalize.
 3. api.rs : slots `Bool` du statement → RÉUTILISENT
    `unf_deferred[k].should_finalize` (plus de re-témoignage).

PRÉDICTION POSÉE PUIS MESURÉE — VERDICT :
 • P1 ✓✓ EXACT : boolslice wrap tête 4→2, tranche 2000..2100 0→10,
   TOTAL 82/82, TOUTES les tranches égales (boolslice n'affiche plus
   aucune ligne).
 • P2 ✓ substance / ✗ octets : les 10 lignes sont émises au bon endroit
   (ancres 1900-2300 : ZÉRO runDiff), mais la ligne rust est (lin,bool)
   là où jsoo a (bool,lin) — pure PHASE héritée de l'amont (jsoo arrive
   avec un y² on-curve pending, nous avec une file vide). Se résoudra
   par l'amont, pas localement.
 • P3 ✓ : init differingRows=0 ; update/merge STRICTEMENT inchangés.
 • P4 ✓ : le @0 (tête) subsiste — j167/r158 désormais (−9 lignes).
 • recorded 21/21.
MÉTRIQUES wrap après : runDiffs 197→196, netGeneric +2→+6 (attendu :
+8 gadgets = +4 lignes, 3216→3220 pile), differingRows 8654→9864
(cascade wiring, toujours trompeur). Répartition des 196 :
  ancres 0-500 : 2 diffs net −8 (@0 −9, @16 +1) ← PROCHAINE CIBLE
  ancres 500-1000 : 5 diffs net +7 (@676 −1, @695 +1, @727 +2,
    @847 +4, @863 +1)
  ancres 1000-1900 : 2 diffs net +7 (@1574 +2, + un autre)
  ancres 1900-2300 : 0 ✓ (la zone du fix)
  ancres 2300+ : 187 diffs NET 0 = phase (voir règle ci-dessus).

PISTES WIRING PARQUÉES ICI (pour la phase wiring, ne pas oublier) :
 • Les x des splits : OCaml refile les VARS de prev_proof_state (cip, b,
   zsrs, zdom, perm — jsoo wire 1765.3 vers finalize) ; nous
   re-témoignons des vars fraîches (api.rs:740, self-loop 4374.2).
   Gates identiques, WIRING différent. Réutiliser les vars comme pour
   les Bool — mais notre UnfDeferred n'a PAS zsrs/zdom (on ne témoigne
   que 8 champs hors bp ; OCaml en témoigne 10 dans l'ordre du spec :
   [cip;b;zsrs;zdom;perm], digest, [β;γ], [α;ζ;ξ], bp16, bool).
   L'ORDRE de témoignage diffère aussi (indices de vars ⇒ wiring).
 • Slots `Packed` (digest/challenges/bp) : mêmes re-témoignages frais
   (api.rs:751) vs refil OCaml — même chantier.

## ✅✅ TÊTE DU WRAP RÉSOLUE — runDiffs 196 → 17 (trois sous-fixes)

Le trou @0 (−9 lignes) était TROIS choses, toutes identifiées au littéral
puis mesurées à zéro (ancres 0-500 : 0 runDiff, le @16 +1 a disparu
aussi, et la queue de phase net-0 est passée de 187 → ~12 diffs) :

 1. **`is_base_case` SUPPRIMÉ** : notre `proofs_verified.equal(0)`
    (~5 gadgets) n'existe pas chez OCaml — le paramètre wrap_main était
    même `_is_base_case` (inutilisé). Pure invention de notre port.
 2. **`prev_step_accs` DÉDUPLIQUÉ** : OCaml n'a QU'UN exists
    (wrap_main.ml:301-305, 2 points) qui sert à la fois de `~sg_old` et
    d'accumulateur par proof dans les hashes (:425-431). Nous témoignions
    4 points (sg_olds + u.prev_step_acc) → +4 lignes on-curve et des vars
    dupliquées (wiring). Les valeurs coïncident position par position
    (dummies front-padded identiques) — assert ajouté dans api.rs.
 3. **SÉLECTION DU DOMAINE WRAP EN CIRCUIT** (wrap_main.ml:352-368) :
    OCaml témoigne `Req.Wrap_domain_indices` (un vecteur, AVANT tout
    gadget), puis PAR PROOF (Vector.map = descendant) :
    `One_hot_vector.of_index index ~length:3` + `Pseudo.Domain.to_domain`.
    • `of_index` (one_hot_vector.ml) = init DESCENDANT de
      `Field.equal (of_int j) i` **+ `Boolean.Assert.any`** =
      assert_non_zero(somme) = witness inverse + r1cs (somme, inv, 1) —
      le gadget `0001-` observé. ~9 gadgets/proof.
    • `all_possible_domains` = log2 ∈ **[13;14;15]**
      (wrap_verifier.ml:59-64, common.ml:25-30) ; index = log2 − 13
      (`actual_wrap_domain_size`). max_log2 = 15.
    • to_domain : shifts = CONSTANTES (optim all-the-same, pseudo.ml),
      generator = lincom masquée (0 gate à la sélection),
      vanishing_polynomial à l'USAGE = 15 carrés + 3 mults (b·pow) + seal.
    IMPLÉMENTATION : l'infra du step (tâche #6) a TOUT servi —
    `FinalizeDomain::Selected`/`SelectedDomain` (ft_eval_circuit.rs).
    wrap_main fait un pass-0 (indices puis one_hots en ordre inverse,
    Assert.any copié du pattern validé api.rs:588 — ordre (somme, inv,
    1)) et la boucle finalize reconstruit FinalizeParams { domain:
    Selected([13,14,15], which) } (FinalizeParams est devenu Clone).
    PerUnfinalized porte `wrap_domain_index` (valeur), rempli par api
    depuis finalize_domain.log2 − 13.

MÉTRIQUES après (recorded 21/21, init 0, update/merge inchangés) :
  wrap runDiffs **17**, netGeneric +22, differingRows 8482.
  Restants, cartographiés lignes exactes :
  • FINALIZE +11/proof : @788 j630/r638 (+8, rows ~1768) et @908
    j109/r112 (+3, ~1997) ; miroir proof1 @1696/@1816. Notre chemin
    Selected émet PLUS que jsoo dans la linéarisation — suspects :
    `pow_circuit(zeta, 2^srs_log2)` EAGER (ft_eval_circuit.rs:262) vs
    OCaml LAZY (plonk_checks.ml:294 forcé :367/:436), et les inverses
    du générateur (div_var vs `one/gen` OCaml), et l'ordre/nombre des
    seals autour du vanishing.
  • X_HAT ±0 net mais mal PLACÉ : 11 ancres CompleteAdd avec j2/r0
    (rows j5133..8783) + un +24 à @2536 (j4967/r5013). Ce sont les 11
    termes 255-bit (5 splits × 2 proofs + digest msgs) : OCaml émet les
    4 gadgets de `scale_fast2'` (exists (s/2,odd)+bool+`2y+odd=s` ;
    top-bit=0 ; n_acc=s) PAR TERME, dans le fold, juste avant le
    CompleteAdd du terme (wrap_verifier.ml:950-955 → plonk_curve_ops.
    ml:254-278). Nous les consolidons en un bloc en amont (+24). ⇒
    Déplacer l'émission par-terme dans public_input.rs (le fold), pas en
    pré-passe.

## ⚠ RÉFUTATION n°4 : lagranges OneHot LAZY (tentative re-revertée)

CONTEXTE : après le fix tête, restait au x_hat une RELOCALISATION net 0 :
nos seals de sélection one-hot concentrés en un bloc +24 (50 lignes
`statement_terms`, rrow≈4963-5013) vs jsoo 2 lignes par terme 255-bit
juste avant son CompleteAdd (11 ancres j2/r0, rows j5133..8783).

TENTATIVE : retirer le seal précoce dans `statement_terms::next`
(OneHot) et laisser les CONSOMMATEURS seller (add_fast selle ses deux
points, scale_fast_core selle sa base :142-143 — comme OCaml
plonk_curve_ops.ml:12/:133). PRÉDICTION : bloc +24 fond, les 11 j2/r0 se
dissolvent, runDiffs 17→~6.

MESURE : runDiffs 17→**288**, netGeneric +22→**+88** (+66 lignes!). La
VIEILLE mesure du commentaire (+26→+84) disait déjà pareil — j'aurais dû
la croire. REVERTÉ (git checkout public_input.rs).
⚠ La mesure était EN PLUS contaminée : le build avait ramassé l'édition
zeta_to_srs concurrente (@788 disparu, @1574 à −1) — les chiffres exacts
sont inattribuables, mais le +66 net global de la partie x_hat est réel.

MÉCANISME SUSPECTÉ (à vérifier au littéral AVANT toute nouvelle
tentative) : la base d'un terme Packed est consommée DEUX FOIS dans
scale_fast2 (OCaml :236-252) : sellée DANS scale_fast_unpack (:133,
copie locale), puis l'ORIGINALE re-négée `add_fast h (G.negate g)` à
:252 (branches strictes). Avec une base LINCOM, chaque consommation
re-matérialise. OCaml paie aussi ces deux coûts — donc notre +66 vient
d'un TROISIÈME endroit à nous (Point::select ? chaîne des corrections ?
notre scale_fast2 :393 ?). ⇒ PROCHAINE SONDE : labels du dump raté sur
les +2 en série (@2355+, la chaîne `public_input correction add`
j226/r10 éclatée) pour voir QUELLE consommation explose. La
relocalisation reste OUVERTE (net 0 — sans effet VK tant que le wiring
n'est pas la phase courante… mais les LIGNES diffèrent, donc si:
l'octet-parité l'exigera).

## ✅ FIX : `zeta_to_srs_length` LAZY — un fix, TROIS circuits améliorés

CAUSE (littéral) : OCaml `zeta_to_srs_length = lazy (pow2pow zeta
srs_length_log2)` (plonk_checks.ml:294). Son SEUL site de force
in-circuit est le fold multi-chunk de p_eval0 dans ft_eval0 (:361-368) —
`Array.fold_right ~init:None` ne force qu'à la branche `Some acc`, donc
JAMAIS en single-chunk. Nos évals sont single-chunk partout ⇒ jsoo
n'émet JAMAIS les 16 carrés. Nous les émettions EAGER à la construction
de l'env (ft_eval_circuit.rs:262, avec un commentaire qui prétendait le
contraire de l'autre commentaire du même fichier :167-169 — lequel avait
raison). Vérifié par LCS : le +8 de la linearization était 16 `001-0`
consécutifs labelés env→ft_eval0, et AUCUN bloc symétrique jsoo-only.

FIX : `ScalarsEnvVar.zeta_to_srs_length: Option<FieldVar>` remplacé par
`srs_length_log2: u32` ; `ft_eval0_prefix_circuit` matérialise
`pow_circuit(zeta, 2^log2)` au PREMIER chunk supplémentaire du fold
(memoïsé), à la position OCaml exacte.

MESURE (prédiction posée avant, tenue) :
  wrap : @788/@1696 (+8 chacun) DISSOUS ; runDiffs 17→18 (une paire de
  phase ±1 @1523/@1542 apparue, @1574 passé à −1), netGeneric +22→+5.
  update : @764 +8 → −1 ; netGeneric +6→−3.
  merge : @765 +9 → disparu ; netGeneric +13→−5 ; runDiffs 121→120.
  init : 0. recorded 21/21.

RESTANTS wrap (18) : @847/@1694 (+3 par proof, région perm scalar/perm
check — fenêtre bruitée, à relire après le prochain fix), la
relocalisation x_hat net-0 (bloc +24 vs 11×j2/r0, voir réfutation n°4),
et des ±1 de phase. STEP : @6 (−4, 3 circuits, recursive_step.rs:4420),
@892 (+2), et des ±1.

## ═══ BILAN DE SESSION (2026-07-17, suite) — runDiffs 111/121/197 → 36/41/18

COMMITS (ordre) : 616ddb5cd3 (split_field à l'éval d'argument + Bool
réutilisés), 64c975348b (tête wrap : −is_base_case, dédup prev_step_accs,
domaine wrap sélectionné en circuit), 045f7d3f63 (zeta_to_srs_length
lazy), 03c5d7e2a9 (Assert.any + claimed-first step-path), 5fcc5ce181
(dédup equals wrap-path), 478fe699a1 (chaîne zetaw d'abord dans
b_actual). recorded 21/21 à CHAQUE étape ; init byte-identique partout.

SCOREBOARD (runDiffs / netGeneric / differingRows) :
  début session→ fin : update 111/+6/7296 → **36/−12/7440**
                       merge  121/+13/15309 → **41/−24/14665**
                       wrap   197/+2/8654  → **18/−17/11721**
                       init   0 (canari, jamais bougé)

RÈGLES NEUVES (à réutiliser, toutes vérifiées littéral + mesure) :
 • Ligne Generic kimchi = [NOUVEAU ; PENDING] (plonk_constraint_system.
   ml:1452-1461) ⇒ la répartition en lignes dépend de la PARITÉ amont ;
   une queue de runDiffs net-0 = cascade de phase, ne pas la chasser.
 • Les λ paresseux OCaml (`lazy`) n'émettent qu'au PREMIER force réel —
   chercher le site de force AVANT d'émettre eager (zeta_to_srs_length :
   jamais forcé en single-chunk).
 • `a + (b * c)` : args droite-à-gauche ⇒ le terme DROIT s'émet d'abord
   (chaînes zetaw avant zeta dans b_actual — effet MASSIF sur les runs
   step car les chaînes y sont distinguables).
 • Un DUPLICATA à nous peut MASQUER un manque réel : la dédup des equals
   wrap a fait passer @847 de +2 à −8 — le vrai trou était couvert.
 • `Boolean.Assert.any` = assert_non_zero(somme) SANS gate OR ;
   `Boolean.all` (n≥3) = equal(constante n, somme) — constante en 1er.
 • Les equals de finalize sont CLAIMED-first (cip :1732, b :1755, perm
   plonk_checks:473) SAUF xi (actual-first, :1613).

L'ANOMALIE UNIQUE RESTANTE DES FINALIZE (−8/finalize, LES 3 CIRCUITS —
update @892 j113/r105, merge @893 j114/r105, wrap @847/@1694 j109/r101):
jsoo a ~16 gadgets mult (`001-0`) consécutifs + 2 `c1-00` dans la zone
b/sg_evals que nous n'émettons pas. Piste : une application de
challenge_polynomial (chaîne de puissances 15 carrés + produits) émise
DEUX fois côté jsoo là où nous une (staged closure appliquée 2× ? ou
sg_evals au MAUVAIS endroit chez nous — nos labels `zetaw`/`sg_evals`
apparaissent APRÈS les EndoMulScalar alpha/zeta du proof suivant,
jsoo AVANT). ⇒ SONDE À FAIRE (session suivante, contexte frais) :
  1. rawrange + wires sur jsoo j1981-1990 (wrap) : à quoi sont câblés
     les 16 mults (vers les OLD challenges ⇒ sg_evals ; vers les NEW ⇒
     b_actual ; vers zetaw ⇒ chaîne zetaw).
  2. Compter les gadgets d'UNE application challenge_polynomial_circuit
     chez nous (labels) vs le bloc jsoo.
  3. Vérifier l'ORDRE de nos émissions de tête de finalize_deferred vs
     OCaml Step 1-6 : map_plonk_to_field (EndoMulScalar α/ζ),
     zetaw (mult gén. masqué), sg_olds/sg_evals (chaînes anciennes),
     digest absorb… — wrap_verifier.ml:1529-1546. Nos zetaw/sg_evals
     semblent DÉCALÉS après les to_field.
RESTE AUSSI : step @6 (−4, domain_for_compiled : equals DESCENDANTS
distinguables par constantes 10/14/15 — notre SelectedDomain::create est
ascendant — ET des mults jsoo en plus, peut-être l'Opt_sponge du
challenge_digest) ; @764 (−1 phase) ; paires CompleteAdd ±1 (phase) ;
wrap : famille relocalisation x_hat net-0 (réfutation n°4 documentée),
@1523/@1542 (±1), @1574 (−1). PUIS : la phase WIRING (leads parqués :
vars des slots Field du statement à réutiliser depuis unf_deferred
[jsoo wire 1765.3], ordre de témoignage unf_deferred = ordre spec OCaml
[5fq;digest;β,γ;α,ζ,ξ;bp16;bool] avec zsrs/zdom witnessés, slots Packed
re-témoignés à dédupliquer).

## ADDENDUM (fin de session) — la sonde du −8/finalize a AVANCÉ :

 • Les 16 mults jsoo (wrap J1982-1988+) = les chaînes pow2pow zeta_n /
   zetaw_n de Step 6 (wrap_verifier.ml:1626-1633, n = Max_degree.
   wrap_log2 = Tock.Rounds = 16), émises INCONDITIONNELLEMENT même en
   single-chunk (le TODO ":1628 zeta_n is recomputed in env below").
   MAIS : nos « dead pow chains » EXISTENT DÉJÀ (finalize.rs:507-521,
   position et longueur correctes). Le −8 n'est DONC PAS les chaînes.
 • La liaison de packing observée (o du gadget k en slot A ligne R →
   gadget k+1 en slot B ligne R+1) est la signature d'une émission
   SÉQUENTIELLE sous la règle [NOUVEAU; PENDING] — utile pour lire les
   chaînes dans les dumps.
 • RESTE INEXPLIQUÉ, sonde n°1 de la reprise : les DEUX gadgets
   `[−big, 1, −1, 0, 0]` (o = y − C·x) à wrap J1981 A et B, câblés vers
   **la ligne 174 cols 4-5** (tête du premier finalize — les seals de
   map_plonk_to_field ? α/ζ to_field ?). Identifier C (dumper la valeur
   exacte sans troncature) et les vars de la ligne 174. Ils précèdent
   immédiatement les chaînes → probablement le mult zetaw = gén·ζ
   (générateur masqué : C = coefficient d'un terme du mask ?) et/ou un
   seal — comparer à NOTRE émission de zetaw (labels `| zetaw`).
 • Après ça : re-LCS ciblé du run @847 (109 vs 101) maintenant que
   b_actual est zetaw-first — le delta résiduel sera plus lisible.

## ★ LE −8/FINALIZE EST ÉLUCIDÉ (sonde wires J1981) — À IMPLÉMENTER

Les deux gadgets-graines J1981 `[−C, 1, −1, 0, 0]` : C = 0x6819a58283e5
28e511db4d81cf70f5a0fed467d47c033af2aa9d2e050aa0e50 = **−endo mod q**
(le gadget est `o = endo·a + b`). Leurs wires prouvent que A et B
réduisent LE MÊME couple (a,b) (cycle A.l→B.l→174.4 : les états finaux
du train EndoMulScalar rows 167-174 = le to_field de ζ) — c'est-à-dire
LE MÊME LINCOM RÉDUIT DEUX FOIS.

MÉCANISME : OCaml `scalar_to_field` = `SC.to_field_checked` retourne le
LINCOM LAZY `a·endo + b` (les rows EndoMulScalar ne produisent pas de
var finale). `map_plonk_to_field` (wrap_verifier.ml:1485-1489) ne SELLE
que les challenges simples (β,γ via ~f:Util.Wrap.seal) — PAS les scalar
challenges (~scalar:scalar_to_field, α,ζ) ni ξ/r (:1616-1618). Donc
CHAQUE usage de ζ/α/ξ/r re-réduit le lincom = 1 gadget `[endo,1,−1]`
à CHAQUE site de consommation : zetaw (S2), sg_evals (S3), zeta_n (S6,
×2 le même — J1981 !), env/vanishing (S7), cip (ξ, r), b_correct (r)…
≈ 16 gadgets = 8 lignes par finalize. NOUS, on selle le résultat de
scalar_to_field UNE fois ⇒ −8/finalize sur les 3 circuits (update @892,
merge @893, wrap @847/@1694 — tous j−8 exactement).

FIX À FAIRE (début de prochaine session, changement LARGE) :
 • notre `scalar_to_field` (scalar_challenge.rs) doit RETOURNER le
   lincom lazy (endo·a + b, pas de seal/gadget de clôture) ;
 • chaque consommateur re-réduit naturellement (notre reduce à l'usage
   existe — cf. la réfutation lazy-lagrange : c'est le même mécanisme,
   ici il joue POUR nous) ;
 • ATTENTION aux 16 bp-challenges (compute_challenges) : usage unique
   chacun ⇒ même nombre de gadgets mais POSITION déplacée (dans les
   chaînes b_actual au lieu du site to_field) — prévoir le déplacement
   dans la prédiction ;
 • ATTENTION : β/γ SONT sellés (seal explicite) — ne pas les laisser
   lazy ; et le step (step_verifier.ml:~994+) a la même structure.
 • PRÉDIRE : +8 lignes/finalize chez nous, dissolution de @892/@893/
   @847/@1694 ; vérifier par le motif [endo,1,−1] dupliqué chez nous
   aux mêmes positions que jsoo (dont le doublon J1981).

## ⚠ RECTIFICATIF immédiat de l'entrée précédente (vérifié au littéral)

Notre `scalar_to_field` retourne DÉJÀ le lincom lazy (scalar_challenge.
rs:285 `a.scale(endo) + b`, aucun seal). Le fix n'est PAS là.

LE VRAI MÉCANISME du doublon J1981 (A et B = même (a,b)) : OCaml
`Field.square x` = `mul x x` et le backend snarky RÉDUIT CHAQUE OPÉRANDE
SÉPARÉMENT — le même lincom passé deux fois ⇒ DEUX gadgets de réduction
identiques `[endo,1,−1]`, PUIS le square. Notre `square_circuit` (et
possiblement notre mul) ne réduit qu'UNE fois un opérande dupliqué (ou
seal partagé). Chaque `mul lincom lincom` (et chaque première
consommation double d'un lazy) nous fait donc émettre 1 gadget là où
jsoo en émet 2 — accumulé ≈ 16 gadgets = les −8/finalize.

⇒ FIX RÉEL (prochaine session) : aligner la sémantique de réduction de
notre mul/square (snarky/src, expr_eval::square_circuit) sur OCaml :
réduction PAR OPÉRANDE, sans partage même si les opérandes sont le même
lincom. Vérifier d'abord au littéral snarky OCaml (checked.ml `mul` /
`square` → reduce_to_v ×2 ?) puis mesurer sur le motif J1981 (notre
côté doit produire le MÊME doublon). Impact potentiellement large
(toutes les mults sur lincoms de tous les circuits) — init=0 comme
canari, et attention aux endroits où nous avons DÉJÀ compensé (des fixes
passés pourraient avoir absorbé cette différence localement).

PRÉCISION FINALE (littéral plonk_constraint_system.ml:1554-1579) :
`reduce_to_v` mémoïse les CONSTANTES (`cached_constants`) mais PAS les
lincoms — chaque CONTRAINTE re-réduit son opérande lincom. Et
`Square (a, c)` ne réduit `a` qu'UNE fois par contrainte — le doublon
J1981 vient donc de DEUX contraintes consécutives consommant chacune le
ζ brut (zeta_n S6 + un autre site à identifier ; zetaw S2 avait déjà
consommé ζ une 1re fois).
⇒ REPRISE : (1) chercher si NOTRE chemin de réduction (RunState /
add_constraint côté rust) MÉMOÏSE les réductions de lincoms — si oui,
c'est LA différence : la désactiver (re-réduction par contrainte, iso
OCaml) en gardant le cache des constantes ; (2) mesurer sur le motif
J1981 (notre dump doit produire le même doublon [endo,1,−1] ×2) ;
(3) init=0 en canari — impact potentiellement TRÈS large.

## ★ GATE zkapp-rust (VkParity.check, 4 backends) — le chemin COMPILE diverge

Le gate `/home/eddy/Projects/zkapp-rust/contracts/src/VkParity.check.ts`
(réf jsoo = o1js **2.15.0 upstream**) a révélé, sur le square minimal
(publicOutput-only, 1 mul) :
 • jsoo local = upstream = `73665795…45675` ✓ (nos bindings jsoo fidèles)
 • rust chemin DIRECT (proveBaseCase / rust-pickles-vk-parity.ts) =
   `73665795…45675` = **FULL MATCH** ✓✓ (28/28 commitments)
 • rust chemin **Program.compile** (compileRecordedProgram → pipeline
   program partagé mina-runtime) = `20282053…44794` ✗ — DEUX PIPELINES
   RUST, DEUX VK. A/B : avec/sans privateInput → aucun effet (les deux
   variants donnent la même VK par backend) ; le zkApp mono-méthode via
   le MÊME chemin compile matche pourtant (hash 24921192…, avec
   ZkappPublicInput). Le discriminant reste à confirmer.
HYPOTHÈSE PRINCIPALE : le pipeline program compile un wrap à LARGEUR
FIXE (max 2 → domaine wrap 2^15) même pour un programme non-récursif,
là où jsoo/le chemin direct font le wrap width-0 (2^13,
actualWrapDomainSize=0). ⇒ SONDE : décoder la VK `20282…` du chemin
compile champ par champ (codec du rapport parity) — si
actualWrapDomainSize/wrap divergent, corriger la sélection de largeur
du pipeline program (recursive_step / compileRecordedProgram) pour
suivre OCaml (largeur = max réel du programme). ⚠ le zkApp qui matche
via compile est CONTRADICTOIRE avec l'hypothèse largeur-fixe simple —
peut-être une différence de STATEMENT (2 champs d'entrée vs sortie
seule) qui change la branche du pipeline. À trancher par le décodage.

CONTEXTE o1js DE CETTE PASSE (non commité) : branche rust ajoutée dans
SmartContract.compile (zkapp.ts, jalon compile+VK, provers stub),
garde d'enveloppe legacy retiré de verify() (zkprogram.ts:152),
smoke test N0 mis à jour, pin mina-rust bumpé e1f10bba→3321d0a9,
benchs: tmp-bench-native.ts, tmp-zkapp-vk-iso.ts, tmp-square-ab.ts,
tmp-square-parity.ts. Roundtrip toJSON→verify des preuves rust: encore
cassé (préfixe présent, rejet plus profond — non résolu).
BENCH NATIF (3 méthodes, sans cache): rust compile 11,6s / jsoo 16,5s ;
prove N0 1,9s / N1 3,5s / N2 3,2s. zkApp: rust compile 1,9s vs jsoo
4,2s, VK iso (hash 24921192…).

## ÉTAT FINAL DE LA PASSE o1js/zkapp (suite du gate 4-backends)

DÉCOUVERTE CLEF : `./run` ne rebuild QUE le fichier de test, JAMAIS la
lib (dist/ datait de la veille) — toutes les mesures o1js du début de
passe tournaient sur une lib périmée. `npm run build` obligatoire après
toute édition de src/lib. (Le « FULL MATCH zkApp » initial était
jsoo-vs-jsoo pour cette raison.)

APRÈS REBUILD, MESURES AUTHENTIQUES (natif) :
 • GATE SQUARE (zkapp-rust, réf o1js 2.15.0 upstream) : **VERT** —
   rust-native = jsoo-native = 7366579…45675. Fix : router les
   programmes tout-N0 du chemin mina-runtime vers le per-branch width-0
   (rust-pickles-recorded.ts, miroir de la règle du chemin direct).
   Cause d'origine : le pipeline program partagé bootstrap width≥1
   (VK 20282053…, maxProofsVerified=1, wrap 2^14).
 • verify()/roundtrip JSON des preuves rust : RÉPARÉS (garde d'enveloppe
   legacy retiré + lib rebuildée) — smoke N0 tout vert.
 • zkApp simple (SmartContract.compile branché rust — NOUVEAU, zkapp.ts):
   compile 1,85 s, enveloppe canonique, VK **diverge** :
   rust 10211940… vs jsoo 24921192…. Deux tolérances analyze ajoutées
   (le recorder EXÉCUTE les closures witness, jsoo non) : instance Mina
   éphémère à comptes dummy pendant le record, et fallback Field(0)
   dans ProofAuthorization.setKind sous inAnalyze.
 • Contrat SIDE-LOADED (test NEUF zkapp-rust :
   SideLoadedZkapp{Jsoo,Rust}.ts + SideLoadedVkParityChild.ts) :
   compile rust OK (DynamicProof + vk s'enregistrent), VK diverge :
   rust 20829101… vs jsoo 2268640….
 • add récursif : diverge (23669624… vs 10959392…) — c'est la tâche #9
   (le −8/finalize lincom per-constraint, plan au carnet plus haut).

PROCHAINES CIBLES, dans l'ordre :
 1. add récursif = reprendre la tâche #9 côté proof-systems.
 2. zkApp/side-loaded : diff de gates des circuits account-update
    (dumper le recorded circuit rust vs le dump jsoo du même
    contrat — même méthodologie ancres/runs que toute la session).
 3. wasm (après le natif, décision utilisateur).
o1js NON COMMITÉ : zkapp.ts (branche rust + 2 tolérances),
rust-pickles-recorded.ts (bypass width-0), zkprogram.ts (verify),
mina-runtime-zkprogram.ts (smoke), pin src/mina-rust (Cargo.lock),
tests tmp-*. zkapp-rust NON COMMITÉ : les 3 fichiers side-loaded.

## ★ zkAPP STEP : la cause des 286 Poseidon manquants est TROUVÉE

Diff step zkApp (harness NEUF o1js src/tests/tmp-zkapp-gates-diff.ts,
deux passes MODE=jsoo/rust ; dumps /tmp/claude-1000/zkapp-gates-*.json):
  jsoo 1024 gates {Generic:103, Poseidon:605, Zero:310, …}
  rust  512 gates {Generic:92,  Poseidon:319, Zero:95, …}
319 = exactement le socle step-verifier (init). TOUT le hachage
account-update manque. Sonde de constance : selfHash est bien une VAR
(pas de pliage constant) mais AUCUNE contrainte → LE RECORDER NE HOOKE
QUE `gates.poseidon` (rust-pickles-recorded.ts:331/:374-385/:458) alors
que `Poseidon.hash` TS passe par **`Snarky.poseidon.update`**
(provable/crypto/poseidon.ts:96 ; sponge :45-53 ; hashToGroup :131) —
jamais intercepté ⇒ vars sans contraintes (BUG DE SOLIDITÉ en plus du
gap de parité).

FIX À IMPLÉMENTER (rust-pickles-recorded.ts, à l'installation des
hooks) : wrapper `Snarky.poseidon` —
 • `update(state, input)` : absorption par blocs de rate 2 ; par bloc :
   témoigner les états de ronde (11 lignes × 3, via la permutation TS —
   constantes poseidonParamsKimchiFp de bindings/crypto/constants.ts)
   avec Provable.witness, puis émettre la contrainte `kind:'poseidon'`
   EXACTEMENT comme le hook gates (:374-385 — lignes de 3 lincoms,
   dernière ligne = sortie), retourner l'état final.
 • sponge create/absorb/squeeze : par-dessus update, sémantique OCaml.
 • hashToGroup : erreur claire si atteint (non requis pour l'instant).
VALIDATION : re-run tmp-zkapp-gates-diff (Poseidon 319→~605), puis
l'écart résiduel Generic/Zero par ancres/runs ; puis
tmp-zkapp-vk-iso (cible : hash jsoo 24921192…) et le test side-loaded
(zkapp-rust, cible 2268640…). Les deux autres flags posés cette passe :
inCheckedComputation ajouté au snarkContext du record (zkapp.ts), et
les deux tolérances analyze déjà commitées (e8289c733).

ÉTAT COMMITS : o1js e8289c733 ✓ ; zkapp-rust 46a2ffd ✓ ;
mina-rust a0a38b48 LOCAL (push https refusé sans askpass — à pousser à
la main). Probe zkapp.ts checkPublicInput ACTIVE (BENCH_DEBUG) — à
retirer avant commit suivant.

## ✅✅ ZKAPP ISO ATTEINT (2e cas) — deux fixes recorder décisifs

 1. Hook `Snarky.poseidon.update` (o1js 5cf006477) : le recorder rendait
    des vars NON CONTRAINTES pour chaque Poseidon.hash (trou de solidité
    + 286 lignes manquantes). Il témoigne maintenant les 55 états de
    ronde (kimchi : sbox→MDS→+rc, pas d'ARK initial, rate 2, pad zéro,
    input vide → 1 permutation) et émet la contrainte poseidon (11
    lignes + Zero de sortie). Histogramme step zkApp : IDENTIQUE.
 2. Indices denses = ORDRE D'ALLOCATION (o1js hook enterAsProver) :
    l'assignation à la première-contrainte inversait l/r des adds
    d'absorption (7 lignes wiring-only). RÈGLE : reduce_lincom trie par
    index de var ⇒ l'ordre des indices doit suivre l'allocation jsoo.
RÉSULTAT : step SimpleZkapp FULL MATCH (1024 gates, 0 ligne) ; VK zkApp
BYTE-IDENTIQUE (hash 24921192…) ; compile rust 2,0 s vs jsoo 4,2 s ;
canari square intact (7366579…).
RESTANTS : side-loaded (rust 5002117… ≠ jsoo 2268640… — pv=1 ⇒ wrap
récursif largeur 1 ; refaire son diff de STEP avec le harness
tmp-zkapp-gates-diff adapté + la parité récursive) et add (tâche #9 —
le plan lincom per-constraint du carnet). Les hooks poseidon/allocation
peuvent AUSSI avoir rapproché le add (les steps update/merge absorbent
des hash) — RE-MESURER le gate add avant d'attaquer #9.

## ✅ Enveloppe VK programme : max_proofs_verified corrigé (e55d208f9b)

L'intuition utilisateur (« leur résultat est juste un encodage base64 »)
était la bonne piste : la VK est du bin_prot base64 DÉCODABLE, et le
décodage champ-par-champ du add (o1js tmp-add-vk-decode.ts) a montré
jsoo max=2 / rust max=1 : `SideLoadedVerificationKey::new` écrasait max
avec la valeur dérivée du DOMAINE du wrap (2^14→N1) au lieu du max des
branches (OCaml Pickles.compile déclare max=2 même en wrap 2^14).
Fix : `from_wrap_verifier_with_max` + l'enveloppe programme passe le max
réel. recorded 21/21. Après bump du pin + rebuild mina-runtime :
maxProofsVerified 2/2, actualWrapDomainSize 1/1 ✓.
RESTE pour add/side-loaded : commitments 0/28 = les OCTETS des circuits
(update 36 / merge 41 / wrap 18 runDiffs) — c'est EXACTEMENT le plan
lincom per-constraint déjà écrit (doublon J1981). Pins : mina-rust
Cargo.lock bumpé e55d208f (commit local — push https à faire à la main).

## ✅ b_actual RÉSOLU (7add2e8100) — zeta_to_srs_length manquait

La divergence @847/@1694 (j109/r101, +8 lignes) N'ÉTAIT PAS
challenge_polynomial (celui-ci matche : pow chain prev.mul(prev) réduit ζ
2× comme OCaml `M.(y*y)`, prod aligné). MÉTHODE qui a tranché :
labels d'émission dans le dump wrap. `dump_recorded_program_circuits`
sérialise déjà `labels` (gate_labels), MAIS seulement si
`SNARKY_KEEP_LABELS=1` (constraint_system.rs:611). Test rust local
`dump_labeled_wrap_for_b_actual_probe` (#[ignore]) qui recharge les
branches add o1js (`/tmp/claude-1000/program-branches.json`, dumpé par le
harness `rust-pickles-program-gates-diff` MODE=rust) ⇒ dump labellisé
SANS napi (cargo test, ~12 s). Décompte endo-reds par label :
  rust b_actual = h_zetaw 15 + r_mul 1 + h_zeta(ζ² 2 + prod 16) 18 = 34
  jsoo b_actual = IDEM 34 (les deux régions 1888-1962 sont IDENTIQUES).
  → le +2 est dans la QUEUE : jsoo row 1981 = un ζ² double-endo (ref 174)
    dans la région perm ; rust y a 0 endo-red. (k=15 des 2 côtés :
    120 EndoMulScalar bp-challenge = 15×8, réfute la piste k=16/zetaw².)
CAUSE : OCaml `derive_plonk` (plonk_checks.ml:429-440) force EAGER
`zeta_to_srs_length = Lazy.force (pow2pow ζ srs_length_log2)` (:436, :294)
en construisant l'enregistrement plonk, même si SEUL `perm` est comparé
(:473 `[ perm ]`). `pow2pow` (:68) élève au carré avec `x * x` (un MUL
qui double-réduit le lincom ζ au 1er pas — le ζ² de jsoo 1981), PAS avec
`Field.square` (≠ la chaîne morte `zeta_n` wrap_verifier:1629 qui, elle,
utilise Field.square = 1 red = notre square_circuit dans les dead pow
chains). En single-chunk `ft_eval0` ne le force jamais ⇒ derive_plonk est
son SEUL site. Notre `ScalarsEnvVar` ne portait que `srs_length_log2` sans
jamais matérialiser la chaîne (commentaire ft_eval_circuit.rs:167-172
« never emitted » — FAUX : cherchait un bloc de 16 carrés, or la chaîne
fait srs_length_log2=8 carrés).
FIX (finalize.rs, après perm_scalar_circuit) : boucle
`zsl = zsl.mul(&zsl)` × env.srs_length_log2, label « zeta_to_srs_length ».
RÉSULTAT : première divergence run-length wrap 847 → 2354 ; b_actual+queue
endo-reds 36 == 36 ; séquence d'ancres identique bout-à-bout ; 21/21.

## ✅ MSM public_input RÉSOLU (1316049a57) — Cond lagrange non scellé

La redistribution net-zero (@2354 −24 correction/statement_terms vs
@2462…@4227 +2 ×12 conditional add) venait de statement_terms
(public_input.rs) qui SCELLAIT chaque point lagrange masqué (chemin
OneHot / domaines step hétérogènes). Or un terme Cond_add utilise son
lagrange UNE fois — `add_fast(lagrange, acc)` — et add_fast scelle
lui-même ses entrées ⇒ le OCaml non scellé (wrap_verifier.ml:334, plain
Vector.reduce_exn) se réduit DANS le conditional add (2 Generic avant
chaque CompleteAdd). Sceller tôt hissait ces 24 lignes dans
statement_terms. FIX : ne sceller QUE les lagranges Packed
(Add_with_correction — ils nourrissent scale_fast2_prime qui re-réduit à
chaque bit). Les Cond passent non scellés à add_fast.
RÉSULTAT MAJEUR : la SÉQUENCE D'ANCRES et TOUTES les run-lengths
Generic/Zero du wrap sont maintenant BYTE-IDENTIQUES à jsoo bout-à-bout
(anchor-walk : 0 ancre divergente, 18→13→0). 21/21.

## 📊 MESURE CANONIQUE — décoder la VK (12/28 après les fixes wrap)

La VK side-loaded est du bin_prot base64 DÉCODABLE (o1js `VerificationKey.data`)
= [2,1] + 7 sigma + 15 coefficient + 6 sélecteurs (28 points Pallas
non compressés, 1796 octets). NE PAS gate-differ 16384 lignes : décoder
les 28 commitments donne DIRECTEMENT quelles colonnes polynomiales
diffèrent. Test rust `decode_and_diff_add_vk_against_jsoo` (#[ignore],
lit /tmp/claude-1000/add-vk-jsoo.bin = base64-decode de add-vk-jsoo.json
`data`, + program-branches.json, compile, compare
`wrap_verification_key_points()`).
ÉTAT après b_actual + public_input (était 0/28) : **12/28 MATCH** :
  ✅ 6 sélecteurs (generic, psm, complete_add, mul, emul, endomul_scalar)
  ✅ coefficient[10..14], sigma[6]
  ❌ coefficient[0..9]  = les coeffs du gate GENERIC (double-generic
     [l1,r1,o1,m1,c1 | l2,r2,o2,m2,c2] = colonnes coeff 0-9)
  ❌ sigma[0..5] = permutation des colonnes témoin 0-5.
INTERPRÉTATION : tous les SÉLECTEURS matchent ⇒ structure des gates OK.
Reste UNIQUEMENT le gate generic (coeffs 0-9) et sa permutation (0-5) ⇒
c'est la PARITÉ DE PACKING (moitiés A/B échangées ⇒ coeffs col 0-4↔5-9
ET wires échangés) + les 1262 vraies ≠ de valeur (linearization/cip).
Le packing est le suspect n°1 (il touche coeffs ET wires en même temps).

## FRONT STEP — update/merge divergent (init byte-identique)

Le même harness labellisé dumpe AUSSI les steps (`R.steps[]`). Diff vs
jsoo (script /tmp/claude-1000/step-diff.mjs) :
  step init (pv0) : fullDiff=0 → BYTE-IDENTIQUE ✅
  step update (pv1) : fullDiff=8485, 1re run-len @ancre 6 (row 282)
  step merge (pv2) : fullDiff=14918, MÊME @ancre 6 (même cause).
Ancre 6 = EndoMulScalar « recursive_step.rs:4604 » (le
scalar_to_field_with_bits 16 bits sur domain_log2). genRun AVANT :
jsoo 204 / rust 200 (+4). Préfixe commun 160 lignes, 1re ≠ à row 237,
région « recursive_step.rs:4553-4564 » = la closure `wt2`
(Other_field.check des shifted-scalar z1/z2) : boucle sur
forbidden_shifted_values_fp_pairs { half.equal(const) (4556) ;
x_eq.and(b_eq) (4558) } ; Boolean::any (4561) ; any.not().assert_equals(1)
(4564). Appelée pour z1 ET z2 ⇒ +2 Generic jsoo par appel (=+4). MÊME
classe que les fixes wrap (placement de gadget equal/and/any). C'est le
front STEP : le step VK absorbé dans le wrap propage ses ≠ dans les
coeff commitments — donc fermer update/merge fait converger coeff[0..9].
FIX #1 (b37ea559be) : `odd.check()` manquait dans wt2 — OCaml
`Other_field.check` (impls.ml:100) fait `typ_unchecked.check t` (Boolean
check du bit odd) AVANT la boucle. Trou de soundness + 1 gate en moins.
step update 8485→7049, merge 14918→14590.
RESTE +3 (run jsoo 205 / rust 202) — PAS dans le equal/and/any de wt2
comme cru, mais AVANT : au dump (rows 235-250), rust bascule à wt2
(recursive_step.rs:4560) dès row 237 alors que jsoo continue le motif
`assert_on_curve` `[1,.,.,.,5|.,.,1,.,.]` (le 5 = constante de courbe
y²=x³+5) sur J237-240 = 2 points de courbe de PLUS. forbidden pairs = 4
(calculé). Les lr sont UNCHECKED (mkpt_unchecked, 4543-4546 — OK), donc
ces assert_on_curve sont sur w_comm/z_comm/t_comm ou delta/sg. Ordre
Bulletproof.typ = lr, z1, z2, delta, sg ⇒ delta/sg APRÈS wt2 (comme
rust). Les 2 points en trop côté jsoo sont donc des commitments
(w_comm/z_comm/t_comm, checkés AVANT lr). COMPTAGE (marqueur coeff 05 =
constante de courbe) : jsoo 101 assert_on_curve, rust 99 (Δ=2), les 2 en
trop aux rows jsoo 237/239 JUSTE avant wt2(z1). RÉFUTÉ : t_comm = 7 chunks
des DEUX côtés (mina_bin_prot.rs:35 `[(Fp,Fp);7]` + assert :380). RÉFUTÉ :
delta/sg APRÈS wt2 (OCaml plonk_types.ml:1436-1440 record openings =
lr, z_1, z_2, delta, challenge_polynomial_commitment ; rust idem). RÉFUTÉ :
prev_challenge_polynomial_commitments checkés à recursive_step.rs:4730,
APRÈS wt2 (= dernier élément du typ per_proof_witness, Vector Inner_curve).
RÉFUTÉ AUSSI (sonde PROBE_MKPT, compteur dans le closure mkpt + marqueurs
de groupe) : les COMPTES de mkpt MATCHENT — par per_proof_witness :
vk_pts 28, vk 28, messages 23 (w15+z1+t7), openings 4 (delta+sg+2
prev_cpcs). Donc AUCUN point manquant, la structure est correcte, PAS de
trou de soundness ici. Le +2 marqueurs @237/239 est donc un décalage de
PACKING double-generic dans la région assert_on_curve/messages (rust
finit les messages ~2 lignes plus tôt que jsoo), PAS des points en trop.

## CŒUR DU RESTE : ordre de PACKING double-generic (step ET wrap)

Constat unifié : partout où ça diverge encore (wrap coefficient[0..9] +
sigma[0..5] ; step update/merge assert_on_curve), les GATES et les
COMPTES matchent, mais les demi-gates sont APPARIÉES différemment dans
les lignes double-generic ([NEW ; PENDING], plonk_constraint_system.ml:
1452-1461). Comme un run générique repart à neuf après chaque ancre
(le pending est flush par un gate non-générique), un même run avec le
même nb de gates devrait s'apparier pareil — SAUF si l'ORDRE d'émission
des sous-contraintes dans le run diffère (une paire (g1,g2) vs (g2,g1)).
⇒ C'est la LONGUE TRAÎNE de la parité byte : aligner l'ordre d'émission
gadget-par-gadget (equal_constraints inversé était déjà un cas ; ici :
assert_on_curve, et les gadgets de wt2/equal/and). PROCHAINE SONDE
CONCRÈTE : comparer `assert_on_curve` rust (l'ordre de ses contraintes
génériques) vs OCaml `Inner_curve.typ`'s check ; puis le premier run
générique qui swappe (wrap row 1895 h_zetaw [endo|plain] vs [plain|endo]).
La VK (decode_and_diff) reste à 12/28 tant que ces appariements ne sont
pas alignés.

## TROIS classes de ≠ résiduelles wrap (first-swap.mjs / pi12.mjs)

1. **row 12 — wiring PI 12** (1re ≠, isolée) : 39/40 entrées publiques
   câblées pareil ; SEULE PI 12 diffère. jsoo câble 8891.col5 → 12.0
   (row 8891 = « x_hat commitment »), rust laisse 8891.col5 en singleton.
   ⇒ le MSM public input rust ne LIE pas PI 12 à son usage (trou de
   contrainte POSSIBLE, ou re-witness au lieu de wire). À AUDITER : est-ce
   que mon fix Cond-no-seal a affecté ça ? (PI 12 = un bit odd de Split ?).
2. **row 90 — valeur** (api.rs:788-799, choose_coordinate.seal) : les
   POINTS de la wrap VK masqués one-hot embarqués dans le step. C'est le
   POINT FIXE circulaire : le step embarque la wrap VK, la wrap absorbe la
   step VK. Ces valeurs convergent AUTOMATIQUEMENT quand la structure
   (gates+wires+packing) matche. Pas un bug séparé.
3. **row 194+ — swaps de packing** (sg_evals, challenge_polynomial) :
   la parité double-generic (cœur, voir ci-dessus).
ORDRE D'ATTAQUE conseillé : (1) auditer/fixer PI 12 (concret, isolé) ;
(3) parité de packing (trouver le 1er flip < row 194 et sa cause d'ordre
d'émission) ; (2) se résout tout seul. Puis re-mesurer decode_and_diff.

## PROGRÈS (fixes de ce tour)

FIX PI 12 (4f5e2168d8) : le digest messages_for_next_step est à la fois
l'entrée publique 12 du wrap ET un élément de step_statement pour x_hat.
OCaml threade le MÊME cvar (pas de witness privé égal). Notre hack
`slot_index == 0` n'est la position (aplatie) du digest QUE dans le cas de
base ; pour update/merge c'est `step_statement_digest_slot =
proofs*(17+TOCK_ROUNDS)`. Donc le digest recevait un witness frais NON
contraint (trou de soundness) + PI 12 restait un singleton de permutation.
Fixé : clé sur la vraie position aplatie. rust câble x_hat 8891.5→PI 12.0
comme jsoo. 21/21.

FIX sg_evals (31712e2d56) : `(sg_evals zeta, sg_evals zetaw)` est un TUPLE
OCaml évalué DROITE-À-GAUCHE ⇒ le vecteur zetaw est émis d'abord. On
émettait zeta d'abord → flip de parité de packing. Swap des 2 boucles :
diff wrap 2279→2102 (coeff 1506→1324, wire 2202→2026), 1er half-swap
194→1326. 21/21.

## PROCHAIN FLIP DE PARITÉ : ft_eval0 @1273

Après sg_evals, la 1re ≠ STRUCTURELLE (hors valeurs circulaires VK
api.rs:806 rows 90-104 = point fixe, se résout à la fin) est row 1273
label ft_eval0 : jsoo émet un endo-red (b1f1) en 1273.A, rust le décale à
1274.B (shift 1 ligne = flip de parité). C'est le 1er `beta.mul(zeta)` du
shift-product de ft_eval0_prefix_circuit (ft_eval_circuit.rs:393-407).
VÉRIFIÉ MATCHANT vs OCaml plonk_checks.ml:372-397 : ft init/fold, shift
product (init a0·zkp·z0, factor gamma+(beta·zeta·s)+w0, acc·factor gauche),
numérateur/dénominateur (term1=(zeta1m1·a1)·(zeta-omzk), term2, (t+t)·(1-z0),
den=(zeta-omzk)·(zeta-1)).
LOCALISÉ (label ft_shift ajouté ft_eval_circuit.rs:393) : row 1272 =
ft_shift (dernier gate du shift-product), rows 1273+ = base loc ft_eval0
= le NUM/DEN (pas le shift-product !). Donc l'endo-red @1273 réduit
`zeta - omega_to_minus_zk_rows` du term1 (`.mul(zeta_minus_omzk)`). rust
insère un gate `[1,0,0,0,0]` (= assert wl=0, wl→1275.1) JUSTE AVANT
l'endo-red → décale de 1 ⇒ flip. jsoo n'a pas ce gate. HYPOTHÈSE : diff
Var-vs-lincom d'une valeur env (omega_to_minus_zk_rows sealed côté OCaml,
lincom côté rust ? ou zeta_minus_omzk réduit une fois de trop). RAFFINÉ (labels ft_shift + ft_numden ajoutés) : les 4 endo-gates du
num/den sont à J[1273.A,1275.A,1278.A,1279.B] et R[1274.B,1275.A,1278.A,
1279.B] — SEUL le 1er (term1 `.mul(zeta_minus_omzk)`) diffère (décalé
d'1), les 3 autres alignés. Les rows ft_shift 1270-1272 MATCHENT
exactement (même pending state en entrée du num/den), et toutes les ops
term1/2/num/den matchent OCaml op-par-op. `zeta_to_n_minus_1` est SEALED
(Var, ft_eval_circuit.rs:143). ⇒ le flip est une subtilité de PACKING
double-generic (pending slot) à la frontière ft_shift→num/den que
l'analyse STATIQUE ne résout pas (mêmes gates, même compte, appariement ≠).
PROCHAINE SONDE (runtime) : instrumenter plonk_constraint_system
`add_generic_constraint` pour logger l'état pending (row courant, half
A/B) à chaque gate autour de 1272-1274, rust vs une trace équivalente ;
OU comparer si `env.omega_to_minus_zk_rows` (=omegas.omega_to_zk) est
Var/lincom vs OCaml. decode_and_diff toujours 12/28 (bougera quand toute
la parité est alignée ⇒ point fixe VK converge). Labels ft_shift/ft_numden
gardés (diagnostic, aucun effet circuit).
RAPPEL : la VK ne bougera (>12/28) que quand le STEP diff atteint 0 (le
wrap absorbe la step VK). Mesurer avec `decode_and_diff_add_vk_against_jsoo`.

## ITÉRATION EN COURS — parité de PACKING double-generic + wiring (wrap)

La structure run-length est byte-identique, MAIS il reste 2279 lignes
coeff/wire différentes (avant fixes : ~11721, tout le cascade run-length
a disparu). full-diff (typ+coeffs+wires) : coeff-diffs 1506 (1er @90),
wire-diffs 2203 (1er @12). CE SONT DES DIVERGENCES PRÉ-EXISTANTES
démasquées, PAS causées par les 2 fixes. Deux sous-classes :
  Sur 1506 lignes Generic à coeffs ≠ : 244 sont des SWAPS de moitiés
  (parité), 1262 sont des VRAIES ≠ de valeur. Sur 40 entrées publiques,
  39 câblées identiques, 1 seule diffère (PI 12).
  1. PARITÉ DE PACKING double-generic (244 swaps). Ex. row 1895 (h_zetaw) :
     jsoo=[endo|plain], rust=[plain|endo] — MÊMES 2 gadgets, moitiés
     A/B ÉCHANGÉES. C'est le « kimchi Generic row = [NEW ; PENDING] »
     (plonk_constraint_system.ml:1452-1461) : un flip de parité du slot
     pending persiste et fait permuter les moitiés en aval.
  2. VRAIES ≠ de VALEUR (1262, la MAJORITÉ). Concentrées linearization
     550, cip fold 282, statement_terms 226, sg_evals 166… — ce sont des
     régions qui ÉVALUENT / ABSORBENT des données du STEP (linearization
     du step, vk index absorb). Row 90 (api.rs:794) coeff[0] jsoo a616dc…
     vs rust 5901489e… (PAS une négation ni un swap). ⇒ le wrap encode la
     VK/linearization du step ; il ne sera byte-identique QUE quand les
     circuits STEP le sont (update 36 / merge 41 encore ouverts). C'est
     le VRAI prochain front : diff des STEP avec le harness labellisé.
  3. PI 12 (1 wire) : jsoo 12.0→8891.5 (usage), rust 12.0→self. Localisé.
PROCHAINE SONDE : trouver le PREMIER flip de parité (row 5/12) et sa
cause (un add_generic_constraint en trop/en moins ou dans un ordre
différent tôt dans le wrap) ; puis diff des STEP (update/merge) avec le
même harness labellisé — le wrap ne sera byte-identique que si les steps
le sont aussi (leur linearization + statement se propagent). Ancre finale
VK_HASH jsoo 10959392966233509715748678308838967246207769407061667940269890557862386195723.
OUTILS : `SNARKY_KEEP_LABELS=1 cargo test -p pickles --release --test
recorded dump_labeled_wrap_for_b_actual_probe -- --ignored` (dump wrap
labellisé, ~12 s, sans napi ; lit WRAP_BRANCHES_JSON) + scripts
/tmp/claude-1000/{sep-diff,diff-dist,coeff-inspect,full-diff}.mjs.

## ★ CAMPAGNE WIDTH-1 (#13 volet 1) — 2b-part2 LANDÉ, init pv0 BYTE-IDENTIQUE

Deux commits (35d1517823 piece i, 0ff0602491 piece ii) terminent le
volet « shape » :

- **Stockage/dispatch** : `RecordedCompiledProgram` = enum
  `{ W2(Shaped<67,2>), W1(Shaped<34,1>) }` sur
  `RecordedCompiledProgramShaped<STEP_PI, ACTIVE>` (API publique
  inchangée, macro `with_program_shape!`). Cycles shapés
  (`RecordedProofInner::ProgramW1`), trait privé `ProgramCycleSlot`
  (pack/unpack des previous), prove n0/recursive génériques (`_arity`
  partout). `prepare_program_recursive_wrap` /
  `_step_from_previous` / `program_unfinalized_from_previous` prennent
  `ACTIVE` (padding « physique » à ACTIVE, padding old-challenges
  protocole à MAX=2).
- **Compile générique** : phase template-dummies via trait
  `ProgramTemplateDummies` — W2 = blob embarqué ; W1 = template du blob
  + bootstrap width-1 prouvé LIVE (`manufacture_bootstrap_step::<34,1>`,
  extension du blob à faire). `compile()` dispatch : max-pv ≤ 1 → W1
  (parité OCaml). Garde-fou : pv d'une branche > ACTIVE = erreur.
- **Wrap_hack porté côté PREVIOUS** : le wrap W1 émet UN vecteur
  old-challenges (largeur programme) ; `program_unfinalized_from_previous`
  le front-pad à MAX avec les dummy wrap challenges canoniques.
- recorded 22/22 — le test pv0/pv1 (`two_field_state`) exerce désormais
  le cycle width-1 N0→N1 complet avec vérif digest side-loaded ✅.

### ⚠⚠ PIÈGE MAJEUR résolu : TROIS binaires rust côté o1js
La régression bench semblait DIVERGER (419/738/34 = signature pré-#11) à
TOUT pin — cause : le dump gates des harnais
(`native.rust_pickles_recorded_program_circuits_json`) vient de
**`@o1js/native-linux-x64` (kimchi_napi.node)**, un TROISIÈME binaire
rebâti UNIQUEMENT par `PROOF_SYSTEMS_ROOT=~/Projects/proof-systems npm
run build:native` — il était rassis (pré-3c060e49). Les trois artefacts
à resynchroniser après tout changement pickles :
1. `npm run build:rust-backend` → mina_runtime.node (backend napi ;
   nécessite pin mina-rust à jour : `cargo update -p pickles` dans
   o1js/src/mina-rust, commit+push du lock) ;
2. `PROOF_SYSTEMS_ROOT=… npm run build:native` → kimchi_napi.node
   (dumps de circuits des harnais gates-diff !) ;
3. `PROOF_SYSTEMS_ROOT=… npm run build:wasm:node:rust` + copie des 4
   kimchi_wasm* → backend wasm.
Triage rapide sans rebuild : `cargo run -p pickles --release --example
profile_compile dump <branches.json> <out.json>` (nouveau mode) — dump
LOCAL, puis diff python vs la référence jsoo.

### ÉTAT (iii) après resync des 3 binaires
- Bench W2 (init/update/merge/wrap) : **FULL MATCH** (neutralité re-prouvée).
- W1 harness (`MODE=rust ./run src/tests/tmp-w1-gates-diff.ts`, réf
  `/tmp/claude-1000/w1-gates-jsoo.json`) :
  - **init pv0 : FULL MATCH** (512 gates, PI=34) ✅
  - update pv1 : PI=34 ✓, 16384 ✓, mais rust +514 Generic +187 Poseidon
    −701 Zero ; 1re divergence STRUCTURELLE : run « Generic 92→94 » puis
    « Generic 81→145 » (+64 = +2 rows ~ 32 témoins ?) avant le 1er bloc
    Poseidon ; +187 Poseidon = +17 permutations.
  - wrap : +21 Generic +77 Poseidon (−98 Zero) = +7 permutations.
- **HYPOTHÈSE PRINCIPALE (à vérifier dans wrap_hack.ml / step_main)** :
  pour un programme width-1, OCaml absorbe le PAD (dummy challenges,
  commitments) du hash `messages_for_next_wrap_proof` HORS circuit —
  état de sponge précalculé (`Wrap_hack.Checked.pad_and_hash` — les
  constantes n'émettent pas de rows) puis absorbe seulement les données
  width-1 réelles ; notre port absorbe la largeur paddée EN circuit
  (17 permutations step + 7 wrap en trop + les rows Generic des témoins
  de pad). Chantier : hash_messages / step-side m4nwrap replay et wrap
  côté sortie — démarrer par la boucle flat-emit rodée avec labels.

## ★ W1 DIVERGENCE LOCALISÉE — Wrap_hack CONFIRMÉ dans l'OCaml (plan de fix)

`src/mina/src/lib/crypto/pickles/wrap_hack.ml` (lu au littéral) :
`Checked.hash_messages_for_next_wrap_proof max_proofs_verified` démarre la
sponge depuis `dummy_messages_for_next_wrap_proof_sponge_states[2 − max_pv]`
(états PRÉCALCULÉS après absorption de 0/1/2 vecteurs dummy en CONSTANTES)
puis n'absorbe QUE les données réelles width-n. Notre
`hash_messages_for_next_wrap_proof` (hash_messages.rs:170) A DÉJÀ le
mécanisme (`dummy_challenges` pré-absorbés hors circuit) — le problème est
que les APPELANTS passent, pour W1, les 2 vecteurs paddés EN circuit
(`hash_dummy_challenges` vide + `hash_old` len 2).

**Fix wrap (prev + new digests), neutre W2 par construction** :
1. `normalize_program_unfinalized` (recursive_step.rs:272) : ajouter
   `active: usize` ; `pad = MAX − active` ;
   `hash_dummy_challenges = old[..pad]` (constantes — la séquence absorbée
   NE CHANGE PAS, donc TOUTES les valeurs de digest restent identiques),
   `hash_old_bulletproof_challenges = old[pad..]`.
   `data.old_bulletproof_challenges` reste la liste MAX (replay finalize).
   6 call sites (recursive_step.rs:3226,3272,3277,3355,3421,3460) — tous
   connaissent ACTIVE.
2. `new_acc_dummy_challenges` (wrap_main.rs:114, digest du NOUVEL
   accumulateur, :361-369) : pour W1 doit valoir `vec![dummy_wrap_chals]`
   (1 vecteur) — trouver le producteur dans api.rs (WrapWitnessData) et le
   brancher sur la largeur du programme.
3. ⚠ PIÈGE var-sharing : api.rs:~976 (`cross_shared` + le test
   `hash_old == old_bulletproof_challenges` → réutilise les cvars du
   finalize pour le hash, iso OCaml). Le split modifie ces égalités pour
   W1 — vérifier ce que jsoo partage à largeur 1 (probablement : le hash
   du slot absorbe les MÊMES cvars que son finalize, sans le préfixe).
4. STEP (+17 permutations ≈ 34 éléments = 15+2+15+2) : le step hashe
   probablement les DEUX groupes m4n à largeur physique 2 — m4nstep
   (hash_messages_for_next_step_proof_opt, commitments+chals à [;2]) ET le
   replay m4nwrap — à passer à 0..ACTIVE. + l'excès Generic (+64 avant le
   1er Poseidon = témoins du pad devenus inutiles).

**Boucle de validation** : après chaque sous-fix, rebuild
`PROOF_SYSTEMS_ROOT=… npm run build:native` (SEUL le kimchi_napi sert au
dump !) puis `MODE=rust ./run src/tests/tmp-w1-gates-diff.ts` ; garde-fou
W2 : `MODE=rust ./run src/tests/tmp-bench-gates-diff.ts` = FULL MATCH, et
recorded 22/22 (dont two_field = e2e W1 prove+verify). État courant : W1
init FULL MATCH ; update +514 Generic +187 Poseidon ; wrap +21 Generic
+77 Poseidon.

## ✅ W1 wrap : Wrap_hack prev-accumulator LANDÉ (Poseidon wrap ALIGNÉ)

`normalize_program_unfinalized` prend `active` et splitte la liste paddée :
préfixe `MAX−active` → `hash_dummy_challenges` (pré-absorbé constant),
suffixe → `hash_old_bulletproof_challenges` (en circuit). Séquence absorbée
inchangée ⇒ tous les digests identiques ; no-op à active=2 (re-vérifié :
bench W2 = 0 diff, recorded 22/22, two_field e2e W1 ok). Le digest du
NOUVEL accumulateur était DÉJÀ largeur-aware (`next_wrap_dummy_challenges`
= préfixe MAX−len, recursive_step.rs:3037→ `new_acc_dummies`).

Mesure W1 après fix (dump local) : wrap histo-delta = {Generic:+15,
Zero:−15} (Poseidon 0 ✓) ; update inchangé {Generic:+514, Poseidon:+187,
Zero:−701}.

**DIAGNOSTIC STEP (+187 Poseidon = ~17 perms = 2×17 éléments)** : les DEUX
hash m4nSTEP du step absorbent la largeur physique 2 au lieu de 1 :
1. per-proof « old digest » (step_verifier.rs:439-457,
   `hash_messages_for_next_step_proof_opt`, inputs
   `messages_for_next_step_accumulators` + `prev_challenges` [;2]) ;
2. « new digest » (step_main.rs:227, hash plain de la NOUVELLE m4nstep).
⚠ CONTRAIREMENT au wrap-hack, côté step OCaml hashe à la largeur RÉELLE
SANS pad → réduire la largeur CHANGE les valeurs de digest : il faut
mettre à jour EN MÊME TEMPS les calculs hors-circuit
(`hash_messages_for_next_step_proof_ref` dans les prepare — vérifier si
les prepare A-driven de la 2a produisent déjà des m4n width-1 côté
VALEURS ; si oui le circuit reçoit peut-être déjà des vecteurs len 1 et
c'est le CÂBLAGE [;2] du circuit main qui force 2). Le +15 Generic wrap
restant et le +514 Generic step : témoins/checks du pad à élaguer — passer
à la boucle labels/flat-emit pour être chirurgical.

## AFFINAGE STEP W1 — deux RÔLES pour les accumulateurs précédents

Le `debug_assert_eq!(messages_for_next_step_accumulators,
prev_challenge_polynomial_commitments)` (recursive_step.rs:4806) n'est un
invariant QUE pour W2, où les deux largeurs coïncident (2) :
- **sg_olds IPA** (`prev_challenge_polynomial_commitments`, masque all-true
  step_verifier.rs:466) : restent à 2 MÊME en W1 — le wrap OCaml PADDE son
  accumulateur (`Wrap_hack.pad_accumulator`, wrap.ml) avec le dummy sg
  VALIDE ; notre prepare fait pareil (recursions padded à MAX,
  recursive_step.rs:3047).
- **old digest** (`hash_messages_for_next_step_proof_opt`,
  step_verifier.rs:439) : absorbe la m4nSTEP du statement PRÉCÉDENT à sa
  largeur RÉELLE = ACTIVE (1 acc + 1 vecteur chals en W1) — SANS pad.
Fix step : passer au digest les DERNIERS `ACTIVE` éléments (convention
front-pad) de messages_accumulators / prev_challenges (+ mask), en gardant
sg_olds/b_poly à 2 ; ET mettre à jour EN LOCKSTEP les digests hors circuit
(`hash_messages_for_next_step_proof_ref` : recursive_step.rs 1292/1315/
1705/1760/2092, api.rs 1618/1918, verify.rs 245, side_loaded.rs 501 — ces
sites doivent trancher par la largeur du PROGRAMME du statement hashé).
Gates de cohérence : two_field e2e (prepare⇄circuit), tmp-w1 harness
(jsoo), bench W2 0-diff. Restant après ça : +15 Generic wrap, +~514−témoins
Generic step (boucle labels).

## ✅✅✅ WIDTH-1 BYTE-IDENTIQUE (volet 1 TERMINÉ au niveau gates)

Trois fixes (après le Wrap_hack prev-accumulator) ont amené le programme
W1 à **0 diff sur les trois circuits** (init 512, update 16384, wrap
16384 — dump local vs `/tmp/claude-1000/w1-gates-jsoo.json`) :

1. **Step — largeur des vecteurs per-proof** (`recursive_per_proof_input`
   prend `active`) : sur le chemin programme, les entrées du hash
   d'accumulateur (points + on-curve checks), les `prev_challenges`
   témoins et le masque (`Vector.trim_front`, step_main.ml:63) passent aux
   DERNIERS `active` éléments ; la liste sg_old IPA reste à 2, préfixe =
   point dummy CONSTANT (`Wrap_hack.Checked.pad_commitments`,
   step_verifier.ml:547). Vecteurs témoins = `Per_proof_witness.typ
   max_proofs_verified` (largeur du programme). → update : 0 diff.
2. **Wrap — partage suffixe** (api.rs) : le hash d'accumulateur réutilise
   les cvars du finalize quand `hash_old` est un SUFFIXE de `old` (le
   préfixe étant passé en constantes pré-absorbées).
3. **Wrap — pad du finalize en CONSTANTES** : nouveau champ
   `WrapUnfinalizedWitnessData.constant_pad_challenges` (posé par
   `normalize_program_unfinalized` = MAX−active) : les vecteurs de pad
   restent DANS le finalize (évalués ET absorbés — l'élaguer coûtait
   −55G/−77P) mais entrent en `FieldVar::constant` → leurs facteurs
   `1 + c·pow` se replient (−15 Generic, exactement l'écart).

Neutralité re-prouvée : bench W2 0 diff (dump local), recorded 22/22
(dont two_field e2e W1). Reste pour le VK parity complet : volet 2
(gadget side-loaded natif — `tmp-sideloaded-gates-diff`) et volet 3
(slots `declareRecordedPreviousState` dans zkapp.ts), puis re-validation
o1js (rebuild kimchi_napi + addon + wasm) et zkapp-rust VkParity.

## ★ VOLET 2 SCOPÉ AU GATE PRÈS — side-loaded (SmartContract + DynamicProof)

Harnais `tmp-sideloaded-gates-diff` après le volet 1 : le zkapp compile
DÉJÀ à PI=34 / 16384 gates des deux côtés (width-1 acquis). Restes :
- step check(pv=1) : jsoo +132 Poseidon, +29 CompleteAdd, −189 Generic ;
  EndoMul/VBM/EMS ÉGAUX (le MSM est déjà iso !).
- wrap : rust +77 Poseidon +22 Generic (la même signature que le pré-fix
  Wrap_hack) — car le slot enfant doit être à la largeur du CHILD
  (maxPV=0 → 0 vecteurs absorbés, pré-absorb 2 dummies, finalize 0 réels)
  et non à la largeur de NOTRE programme (1).

Constat clé : le recorder o1js traite le DynamicProof comme un SelfProof
(pv=1, machinerie standard liée à NOTRE clé wrap) — l'app n'enregistre
que le hash du vk (27 poseidon). Le wrap possède DÉJÀ la sélection
one-hot du domaine par slot (`wrap_domain_index`, wrap_main.rs:126-170).

### Plan d'implémentation (incréments committables)
A. **Plomberie largeur enfant** : RecordedCircuit gagne un descripteur
   par preuve précédente `{ child_max_pv, side_loaded: bool, vk_slots }`
   (o1js l'écrit : DynamicProof → maxProofsVerified, SelfProof → largeur
   du programme). Les prepare/normalize utilisent la largeur ENFANT par
   slot (au lieu d'ACTIVE) pour : hash_dummy/hash_old (wrap),
   constant_pad_challenges (wrap finalize), old-digest/masque/vecteurs
   per-proof (step). ACTIVE reste la largeur du STATEMENT.
B. **Wrap enfant maxPV=0** : devrait tomber à ~0 diff avec A (le domaine
   2^13 passe par wrap_domain_index déjà en place — vérifier la valeur
   posée par les prepare pour un slot side-loaded).
C. **Step gadget side-loaded** (le gros) :
   - vk TÉMOIN par slot (56 coords, on-curve via Inner_curve.typ) au lieu
     du partage `share_index_sponge` avec la clé du programme ;
   - index-sponge absorbé sur les points témoins (+14 perms jsoo) ;
   - x_hat DYNAMIQUE : `public_input_commitment_dynamic` (one-hot sur les
     3 domaines wrap 13/14/15 possibles, step_verifier.ml:558+) — les
     +29 CompleteAdd ;
   - liaison app : les cvars du vk témoin = les fields de l'argument `vk`
     (comme previous_state_slots — vk_slots depuis o1js) ; le hash du vk
     dans l'app (27 poseidon) reste applicatif.
   - old-digest à largeur enfant (0) — via A.
D. Re-validation : sideloaded harness 0-diff, bench W2 + w1 FULL MATCH,
   recorded 22/22, puis zkapp-rust (VkParity + side-loaded key test).

## ★ GADGET SIDE-LOADED STEP — plan d'exécution détaillé (C1..C4)

Wrap sideloaded : histogramme EXACT, 44 rows résiduelles = CONSTANTES
cuites (les valeurs de la VK du step, qui changeront avec le gadget) — se
résoudront SEULES quand le step sera identique. Step restant vs jsoo :
jsoo +319 Poseidon, +326 Generic, +29 CompleteAdd (et rust doit perdre
ses rangées « machinerie standard » là où jsoo utilise le gadget).

Sémantique OCaml (lue au littéral) :
- La VK est TÉMOIGNÉE DANS L'APP (au point d'appel `proof.verify(vk)`,
  via `Side_loaded.in_circuit` → `exists Side_loaded_verification_key
  .typ` : 28 points wrap_index avec check on-curve, + one-hots
  `max_proofs_verified` (3 bools) et `actual_wrap_domain_size` (3 bools)).
- La machinerie per-proof (types_map.For_step.of_side_loaded) :
  `wrap_key` = les points témoins, `wrap_domain = Side_loaded which`
  (one-hot), `step_domains = Side_loaded`.
- verify : index-sponge sur les points TÉMOINS (pas de partage),
  x_hat = `public_input_commitment_dynamic` (step_verifier.ml:373-437 :
  par élément du statement, `select_curve_points` = one-hot × constantes
  lagrange des 3 domaines wrap [13,14,15] (wrap_domains pv∈[0,1,2]),
  puis seal ; version `lagrange_with_correction` (2 points) pour les
  Packed ; les domaines 13≠14≠15 ⇒ le raccourci all-equal (l.387) NE
  s'applique PAS → chemins one-hot).
- finalize du wrap enfant : domaine Side_loaded = sélection one-hot sur
  [13,14,15] (notre infra Pseudo/SelectFrom du finalize step, à brancher
  sur le one-hot du vk témoin).

### Incréments
C1. Nouveau constraint kind enregistré `side_loaded_vk { proof: u32,
    commitments: Vec<u32> (indices aux des 56 coords), max_pv one-hot?,
    domain one-hot? }` — o1js l'émet au point verify(vk) (le vk arg
    fournit les valeurs) ; le replay rust étend : witness des 28 points
    DEPUIS ces aux (les cvars des coords = les cvars de l'app — wire
    union), on-curve 2 rows/pt, one-hots (3+3 bools + asserts) ; stocke
    l'index témoin par slot dans un RefCell côté main pour la machinerie.
C2. Machinerie : si slot side-loaded → dlog_index = index témoin,
    PAS de share_index_sponge (sponge_after_index sur les témoins).
C3. x_hat dynamique (le plus gros) : `public_input_commitment_dynamic`
    — one-hot × constantes lagrange des 3 domaines (SRS tock 2^13/14/15),
    lagrange_with_correction, seal. Emplacement : XHatInput nouveau
    variant dans verify (step_verifier.rs).
C4. finalize domaine enfant : FinalizeDomain::SelectFrom sur [13,14,15]
    avec le one-hot du vk (au lieu du Fixed(2^15 wrap program)).
Validation à chaque incrément : sideloaded harness (dump local kimchi_napi
: PROOF_SYSTEMS_ROOT=… npm run build:native), garde-fous bench W2 + w1
FULL MATCH + recorded 22/22. Les VALEURS de prove side-loaded viendront
après la parité gates (nouveau chemin prove avec DynamicProof envelope).

### C1 — layout EXACT du vk témoin (side_loaded_verification_key.ml:349+)
`typ` (ordre d'allocation) : (1) `max_proofs_verified` One_hot N3 (3
booléens + check one-hot), (2) `actual_wrap_domain_size` One_hot N3, (3)
`wrap_index` = Plonk_verification_key_evals de `Inner_curve.typ` (ordre
standard de notre PlonkVerificationKeyEvals::to_list ; on-curve 2 rows
par point — notre `mkpt`). `to_input` : one-hot 1 = 3 packeds (b,1),
one-hot 2 = idem, puis les 56 coords en fields. Hash =
`Random_oracle.Checked.hash ~init:Hash_prefix_states.side_loaded_vk`
(vérifier le prefix exact + pack_input) ; o1js assert ensuite
`digest == vk.hash` (zkprogram.ts:1467-1469, chemin jsoo).

### Architecture rust retenue (C1)
- Nouveau `RecordedConstraint::SideLoadedVk { proof: u32, vk_hash:
  LinComb }` (serde kind "side_loaded_vk") émis par o1js à la position
  exacte du bloc jsoo (FIN du corps de méthode, boucle sur les
  DynamicProof — zkprogram.ts:1449-1470 ; même bloc côté zkapp.ts).
- Le replay (`RecordedApp::main_with_previous_app_state`) étend le
  marqueur avec le gadget fidèle (valeurs compile : points placeholder
  on-curve (i+1)·G ; prove réel plus tard) et STASH l'index témoin +
  one-hots par slot dans un `Arc<Mutex<Vec<Option<WitnessedSideLoadedVk>>>>`
  partagé avec le circuit (champ du RecursiveStepWidth2Circuit) — l'app
  tourne AVANT la machinerie (app-before-machinery ✓).
- C2 : per-proof side-loaded → dlog_index = index témoin (pas de
  share_index_sponge). C3 : x_hat dynamique. C4 : finalize SelectFrom
  [13,14,15] sur le one-hot domaine.

## ✅ C1+C2 LANDÉS (d2a2c3daf9 + o1js d5902b9b0) — Poseidon step side-loaded EXACT

Le gadget vk-témoin est en place (marqueur `side_loaded_vk` émis par
o1js en fin de corps de méthode ; expansion rust fidèle ; stash
thread-local app→machinerie ; la machinerie réutilise l'index témoin,
sans partage de tag ni réutilisation next-key). Mesure : step Poseidon
2541 = jsoo EXACT (le hash 57-absorbs était juste du premier coup) ;
wrap histogramme exact (44 rows constantes qui suivront le step).
Restes step : jsoo +233 Generic, +29 CompleteAdd, càd :
- **C3 x_hat dynamique** : `public_input_commitment_dynamic` — par
  élément du statement wrap, sélection one-hot (3 domaines 13/14/15) des
  constantes lagrange : b·(x,y) = lincoms (0 row), somme, puis SEAL (2
  rows/point) ; `lagrange_with_correction` = 2 points (g, −g·2^shift) et
  un add_fast en plus (les +29 CompleteAdd ≈ un par élément packé).
  Données : les lagranges des 3 domaines à préparer (tock SRS 2^13/14/15)
  → nouveau champ RecursiveStepData (packed_lagranges par domaine) +
  variant XHatInput dans le verify (step_verifier.rs) branché quand
  side-loaded (le flag `_side_loaded` est déjà dans
  recursive_per_proof_input).
- **C4 finalize domaine enfant** : le finalize du wrap enfant doit être
  `Pseudo.Domain` one-hot [13,14,15] piloté par le one-hot domaine du vk
  témoin (stash), au lieu de Fixed — champs FinalizeDomain::SelectFrom
  déjà existants côté step (utilisés pour les domaines de branches).
Garde-fous après C1+C2 : bench W2 + w1 FULL MATCH ✓.
⚠ REBUILD : le harness sideloaded compile via le blob WASM (3e binaire !)
— `npm run build:wasm:node:rust` + copie des 4 kimchi_wasm* vers dist
obligatoire après tout changement pickles, EN PLUS de build:native.

### C3 — ordre d'émission EXACT du x_hat dynamique (step_verifier.ml:421-478)
1. Partition constant/non-constant des éléments du statement (ordre
   statement). Par élément non-constant, DANS L'ORDRE : 1 bit →
   `assert boolean` (1 row) + `Cond_add(b, lagrange i)` ; n bits →
   `Add_with_correction((x,n), lagrange_with_correction i)` — les
   SÉLECTIONS one-hot (b·L_d en lincomb, 0 row) + SEAL (1 row/coord) des
   points [g; corr] s'émettent ICI, par élément.
2. `correction` = reduce `add_fast` de TOUTES les corrections (k−1
   CompleteAdd pour k termes corrigés).
3. `init` = fold add_fast des points constant_part sur `correction`.
4. Fold principal par terme dans l'ordre : `Cond_add` → `if_ b
   (add_fast g acc) acc` ; `Add_with_correction` → `add_fast acc
   (scale_fast2' g x ~num_bits)` (le scale — nos scale_fast2_prime —
   s'émet DANS le fold, PAS en passe séparée comme multiscale_known !).
5. `negate` (puis blinding +H côté appelant, comme le chemin connu).
Corrections : `lagrange_with_correction ~input_length:n i` = [L_i ;
 −L_i·2^(bits_per_chunk·chunks_needed(n))] par domaine, sélectionnés puis
seal. Implémentation : `public_input::multiscale_dynamic(sys, terms
[(value, num_bits, [L^13,L^14,L^15])], one_hot: [Boolean;3])` + variant
`XHatInput::Dynamic` dans verify ; données = lagranges des 3 domaines
tock (2^13/14/15, SRS::get_lagrange_basis) par slot side-loaded (nouveau
champ RecursiveStepData, rempli quand le slot est side-loaded).
C4 rappel : finalize du wrap enfant en SelectFrom [13,14,15] piloté par
le one-hot domaine du vk stashé (les +~117 Generic restants).

## ★★ C3+C4 CÂBLÉS — side-loaded step : delta = {Generic: −132} SEULEMENT

multiscale_dynamic branché (XHatInput::MultiscaleDynamic, verify_one
switch sur side_loaded_x_hat = (one-hot domaine du vk stashé, lagranges
3-domaines par élément — cache OnceLock `side_loaded_x_hat_lagranges()`
recorded.rs, ATTENTION rounds = RECORDED_N1_STEP_ROUNDS=16 pas TOCK=15)
+ C4 finalize SelectFrom [13,14,15] piloté par le one-hot (domain_log2 =
Σ b_i·(13+i)). Mesure dump local : step check — CompleteAdd/Poseidon/
VBM/EndoMul/EMS TOUS EXACTS ; reste {Generic: −132, Zero: +132} (rust en
MANQUE 132) ; wrap toujours 44 rows constantes (suivront le step).
PISTE pour les 132 : différence entre notre FinalizeDomain::SelectFrom
(re-dérive des égalités one-hot depuis la var domain_log2) et le
`Pseudo.Domain` jsoo sur les booléens du vk ; ou le `assert_16_bits` /
vanishing amount ; localiser à la boucle labels (dump local
SNARKY_KEEP_LABELS=1 + première zone divergente vs jsoo).
Encore à faire ensuite : garde-fous (bench W2, w1, recorded 22/22) puis
commit ; puis wrap 44 rows (auto) ; puis PROVE side-loaded (chemin
DynamicProof envelope) + zkapp-rust suite.

### Localisation des 132 Generic (side-loaded step)
Première divergence typ à la row 446, labels = recorded.rs:590/631/632 =
le LOWERING DE L'APP ENREGISTRÉE (arms Equal/Poseidon du replay), dans la
zone poseidon de l'app (les 27 poseidon du zkapp = hash account-update) :
jsoo [Generic 2, Poseidon 11] vs rust [Generic 3, Poseidon 11], puis
jsoo Poseidon-4 où rust Poseidon-3 — décalages ±1 par bloc. Le total
−132 Generic rust est la SOMME de ces écarts dans la région app.
HYPOTHÈSES : (a) la position/forme de notre marqueur side_loaded_vk
décale les variables de l'app (allocation aux) vs jsoo qui witness le vk
APRÈS le corps ; (b) le recorder o1js émet pour ce code zkapp une
séquence poseidon/generic légèrement ≠ de jsoo natif (à comparer :
l'app zkapp était iso AVANT le side-loaded — vérifier avec le zkapp
NON-side-loaded harness (tmp-zkapp/zkapp-gates dumps) que l'app zone est
toujours iso) ; (c) l'assert digest==vk_hash (Equal) → union de classes
qui change le packing double-generic autour.
Boucle : dumper les VALEURS/coeffs des rows 440-475 des deux côtés,
identifier ce que chaque Generic calcule (les 2 vs 3 avant le 1er bloc
Poseidon), remonter au code o1js correspondant.

### 132 Generic — structure fine (dernière observation de la fenêtre)
Liste des mismatches de runs (0-2500) : petits ±1 (run74 G62→63,
run158 G1→3) puis RÉORDONNANCEMENT à la frontière app→machinerie
(runs 161-170) : jsoo = [G3, P11, Z, G203, EMS1, G90, EMS16, G114,
P11-chain…] ; rust = [G147, EMS1, G146, EMS16, G13, P11-chain…].
Lecture : jsoo émet UN bloc P11 isolé tôt (squeeze du digest vk ?) puis
les témoins machinerie (EMS16 = les 16 challenges), alors que notre
gadget émet [one-hots, 56 on-curve, 29×P11] d'un bloc à la position du
marqueur puis toute la machinerie. L'ORDRE jsoo exact du bloc side-loaded
(`vkToCircuit` → `exists typ` alloue AVANT les checks ? les checks typ
émis où ?) est à établir avec une trace labellisée jsoo (ou par lecture
snarky typ : exists = alloc puis check TOUS ensemble — mais
`inCircuitVkHash` (P-chain) s'émet à l'appel vkDigest, AVANT
`Field(hash).assertEquals` et AVANT `sideLoaded.inCircuit`). Piste : nos
one-hot/on-curve devraient peut-être s'émettre APRÈS la P-chain du hash
(l'ordre exists(typ) : alloc sans rows, hash sur les vars alloués,
checks typ à la FIN ?) — tester en déplaçant les checks. Reprendre ici.

## ★★★ STEP SIDE-LOADED BYTE-IDENTIQUE — wrap à 16 rows

Fixes finaux du step (0 diff / 16384 vs jsoo) :
- of_index du domaine side-loaded émis en DESCENDANT (Vector.init
  droite-à-gauche), constante à GAUCHE ; ones_vector : témoin à gauche.
- `select_curve_points` : seals Y avant X, et pour
  `lagrange_with_correction` la CORRECTION se sélectionne AVANT g
  (Vector.map droite-à-gauche).
- volet 3 : zkapp.ts déclare `previous_state_slots` (union app↔machinerie
  du statement enfant) — commit o1js b32dce93f.
Guards : bench W2 = 0, w1 = 0 (dumps locaux).
RESTE : wrap side-loaded 16 rows (5 clusters « x_hat commitment |
public_input conditional add » rows 2606-3070 + 105 + 4394) —
différences de CONSTANTES dans les cond-adds du x_hat wrap (les 5
clusters ≈ les 5 odd-bits Type2 ? valeurs lagrange ≠). À élucider :
d'où viennent les constantes jsoo ('0262d2e23722…') vs les nôtres.

## ✅✅✅✅ #13 TERMINÉ — VK PARITY TOTALE (gate zkapp-rust 3/3 × 4 backends)

`npm run test:vk-parity` (zkapp-rust) : square, add (récursif) et
**side-loaded zkapp (SmartContract + DynamicProof)** produisent le MÊME
hash VK sur jsoo-wasm / jsoo-native / rust-wasm / rust-native
(side-loaded : 22686407…0736392). Test side-loaded ajouté au gate
(VkParity.check.ts, zkapp-rust ae2fbb6). Dernier fix décisif : le
raccourci all-equal du x_hat wrap ne replie QUE les paires corrigées ;
le `lagrange` simple masque toujours par which_branch
(OneHot{corrected_constant}) ; donor structurel et wraps legacy gardent
Prepared. Harnais o1js : sideloaded + w1 + bench = TRIPLE FULL MATCH.
recorded 22/22. Pin mina-rust 59191898 ; tip 183f0d0177.
NOTE prove side-loaded : le PROVE d'un DynamicProof réel (enveloppe →
witness du gadget vk avec les vraies valeurs + chemin prove side-loaded)
n'est PAS encore câblé — compile/VK seulement.

## ➡ TÂCHE SUIVANTE : #12 — cache des clés prover (iso jsoo, warm 6 s)

Modèle : le chemin base-path existant (rust-pickles-recorded.ts
~1660-1712) : cache_key → readCache → from_cache_bytes → compile →
cache_bytes → writeCache (kind 'step-pk'). À faire pour
RecordedCompiledProgram : exports napi+wasm (program_cache_key,
program_cache_bytes, compile_program_from_cache_bytes), sérialisation
des index (rmp comme le blob template), branchement o1js dans
compileRecordedProgram avec le Cache o1js standard.

## ✅ #12 CŒUR RUST LANDÉ (8c5f980543) — cache clés prover : warm 0,5-0,9 s natif

`RecordedCompiledProgram::{cache_key, to_cache_bytes, from_cache_bytes}` :
payload = index VÉRIFIEURS seulement (step par branche + wrap, rmp,
fixup via template_dummy::fixup_vi rendu pub(crate)) ; restore =
resynthèse via le MÊME flux single-pass (valeurs DONOR — impératif :
from_cached_verifier compare les domaines, et la resynthèse doit être
byte-identique au compile → utiliser structure_vk du donor synthétique,
PAS la vraie clé wrap) + ProverIndex::create(lazy) (column evals
différées au premier prove) + verifier CACHÉ attaché (zéro MSM).
snarky::ProverIndexWrapper::from_cached_verifier. Mesures natives :
bench 5,6→0,54 s, sideloaded 5,3→0,85 s, w1 4,5→0,90 s, VK identiques ;
test prove+verify après restore dans la suite (23/23).
⚠ v1 ProverIndex-payload = 683 MB (column_evaluations sérialisées) —
NE PAS revenir à la sérialisation du prover index.

### RESTE #12 — branchement o1js (mécanique)
1. kimchi-wasm/src/pickles.rs (modèle base ~330-360) :
   rust_pickles_recorded_program_cache_key(branches_json),
   rust_pickles_recorded_program_cache_bytes(&WasmRecordedProgram),
   rust_pickles_compile_recorded_program_from_cache_bytes(branches_json,
   bytes) (run_in_pool).
2. mina-rust backend.rs : ops équivalentes dans l'enum BackendRequest
   (compile_program_from_cache / program_cache_bytes / program_cache_key)
   + napi passthrough.
3. o1js compileRecordedProgram (rust-pickles-recorded.ts ~1500s) : autour
   du compile partagé — cache_key → cache.read (kind 'step-pk'-like
   header custom persistentId=programCacheKey) → hit :
   from_cache_bytes ; miss : compile puis cache_bytes → cache.write.
   Brancher les DEUX chemins (wasm bindings + minaRuntime). Puis mesurer
   warm wasm (attendu ≪ jsoo 6 s) via BENCH_CACHE=default
   tmp-bench-wasm.ts, et valider VkParity+zkapp-rust inchangés.

## ✅ #12 CÂBLÉ BOUT-EN-BOUT (wasm) — cache fonctionnel iso jsoo

o1js compileRecordedProgram passe par le Cache standard (kind step-pk,
programName 'rust-pickles-program', best-effort, invalidation par digest
des branches). kimchi: coefficient-evaluation déférée dans la LazyCache
(un index lazy ne paie RIEN avant le premier prove) ; restore des
branches non-N0 en parallèle. Mesures bench wasm : cold 12,5 s → warm
7,8 s (VK identique) ; jsoo warm 5,5 s. Natif (exemple) : warm 0,5-0,9 s.
Commits : proof-systems 9979f35d23, o1js 839bce8ee.

### Restes #12 (polish)
1. −2,3 s wasm vs jsoo : cacher les BASES SRS brutes sur disque (codec
   v2 comme les lagranges — jsoo a un cache SRS ⇒ iso-jsoo légitime) ;
   la création parallèle wasm coûte ~2,5-3 s au seed.
2. Chemin NATIF (minaRuntime/backend.rs) : ops program_cache_key /
   program_cache_bytes / compile_program_from_cache dans BackendRequest +
   branchement o1js du chemin useMinaRuntimeBackend (le wasm est fait).
3. Le premier PROVE après restore paie la matérialisation lazy des
   column evaluations (~1-2 s par index) — mesurer et documenter.

## ✅✅ #12 TERMINÉ — cache iso-jsoo sur LES DEUX backends, plus rapide que jsoo

- Chemin natif (minaRuntime) : CompileProgramRequest transporte le
  payload de cache (restore avec repli silencieux) + le renvoie sur
  demande ; op ProgramCacheKey. o1js branche via le Cache standard
  (mina-rust e0874da7, o1js …).
- Cache SRS brut (parité jsoo) : codec SRS2 (h + g uncompressed, décode
  parallèle non-validé), seed/export (`rust_pickles_seed_srs/export_srs`),
  fichiers `srs-{curve}-{n}.v2.bin` dans ~/.cache/pickles-rs, seedés
  AVANT tout lagrange (proof-systems 2a18eef5d2).
- Mesures warm (bench 3 méthodes, VK identiques partout) :
  natif 4,7 s • wasm 4,5 s • jsoo 5,5 s → rust warm < jsoo warm ✓.
- Garde-fous : recorded 23/23, triple FULL MATCH gates, VkParity 3/3.
Reste (mineur) : premier prove après restore paie la matérialisation
lazy des column evaluations (~1-2 s/index) ; prove side-loaded réel
toujours à câbler (compile/VK ok).

## Audit perf compile (contrôle "d'où vient la vitesse ?", 2026-07-19)

Question : les chiffres de compile rust sont-ils gonflés par des données
pré-embarquées ? Réponse : **rien n'est embarqué dans les binaires**
(le plan SRS-rkyv est parké, non implémenté). Deux caches DISQUE existent :
`~/.cache/o1js` (Cache o1js standard : clés prover `recorded-program-v1-*`,
gaté par Cache.None — inactif dans les benchs) et `~/.cache/pickles-rs`
(SRS brut + bases de Lagrange, `PICKLES_CACHE_DIR` pour dérouter).

Mesures à froid RÉEL (cache dir vide/absent, Cache.None, AddZkProgram) :
- rust-native 6,1 s • jsoo-native 8,5 s
- rust-wasm 14,5 s • jsoo-wasm 17,1 s
→ rust bat jsoo même 100 % à froid. Avec le cache disque SRS/Lagrange
chaud, rust-wasm descend à ~8,8 s (~5,7 s économisés : group-map série).

Constats structurels (vérifiés empiriquement, dir déplacé) :
1. Le backend NATIF n'utilise PAS le cache disque du tout : le compile
   shaped (`RecordedCompiledProgramShaped::compile`) n'appelle jamais
   `warm_recursion_caches` — seuls les chemins legacy Base/N1/N2 et les
   tests cargo le font. Ses 6,1 s sont un recalcul complet à chaque run.
2. Côté WASM, c'est l'hôte o1js qui seed/persiste ~/.cache/pickles-rs
   (readLagrangeCacheFiles/persistLagrangeCaches) SANS respecter
   Cache.None — contrairement à jsoo dont le cache SRS passe par l'objet
   Cache. Écart de gating assumé (données publiques déterministes,
   neutres pour les VK) mais à documenter dans toute comparaison de bench.

## ✅ #14 TERMINÉ — cache SRS/Lagrange iso-jsoo (fonctionnement ET paramètres)

Le cache SRS/Lagrange rust passe par l'objet `Cache` d'o1js avec les
ENTRÉES EXACTES de jsoo — `srs-fp-65536`, `srs-fq-32768`,
`lagrange-basis-{f}-{taille}` (JSON OrInfinity/PolyComm, version 1) —
partagées octet pour octet dans les deux sens (jsoo chauffe rust, rust
chauffe jsoo), avec le gating de jsoo : `Cache.None` ⇒ rien,
`canWrite` gaté, écriture des seules entrées manquantes.

- pickles e0e64be41d : codecs jsoo (`seed/export_{tick,tock}_srs_jsoo`,
  `seed/export_lagrange_basis_jsoo`) + `set_disk_cache_enabled` (le
  cache disque interne ~/.cache/pickles-rs ne sert plus qu'aux runs
  cargo autonomes ; PICKLES_CACHE_DIR toujours respecté là-bas).
- kimchi-wasm : `rust_pickles_seed_srs/export_srs/seed_lagrange_basis/
  export_lagrange_basis` basculés au payload jsoo.
- mina-rust cf0ba5bb : ops `SeedSrsCache`/`ExportSrsCache` (base64 sur
  le fil), `set_disk_cache_enabled(false)` à l'init du Backend,
  capability `srs-cache-v1`.
- o1js a6f59124f : `readSrsCacheSeeds`/`persistSrsCacheEntries` via
  readCache/writeCache (headers identiques à srs.ts/napi-srs.ts) sur
  les DEUX chemins compile (wasm + minaRuntime) ; le chemin fichier
  direct ~/.cache/pickles-rs est SUPPRIMÉ d'o1js.

Validation (AddZkProgram) : Cache.None ⇒ zéro IO (dir déplacé, rien
recréé), natif 6,1 s / wasm 14,5 s. Cache default : rust-wasm seedé par
les entrées ÉCRITES PAR JSOO → 7,2 s ; rust écrit lagrange-basis-fq-8192
manquante et jsoo la relit (11,0 s, VK id.) ; rust-native via les ops
runtime → 1,4 s à chaud. VK identiques partout ; VkParity 3/3 × 4
backends. Trap habituel : l'addon natif se construit depuis le
SUBMODULE o1js/src/mina-rust — le bumper avant build:rust-backend.

## #15 — suivi bench + verdicts perf (2026-07-19)

Baseline versionnée : zkapp-rust/contracts/BENCHMARKS.md (froid + chaud,
4 backends, gates, commits) — à re-runner à chaque changement de perf.
- Piste « frontière JS↔wasm binaire » : NON-levier, réfutée par mesure
  (branches JSON 0 ms / 1,2 Ko bench, ~450 Ko zkapp). Ne pas y revenir.
- Piste « décodage cache parallèle » : PIÈGE — l'allocateur wasm à
  verrou global rend le parallèle BigUint 3× plus lent (4,3 s vs 1,5 s).
  Correctif retenu : field_from_decimal sans allocation (limbs pile) +
  rust_pickles_seed_srs_cache_batch (une entrée de pool). Seed = 416 ms.
- Décomposition warm compile wasm (2,05 s) : restore pk ~1,1 s (PROCHAIN
  levier compile) • analyzeMethods TS 442 ms • seed 416 ms.
- Levier majeur restant (prove wasm 2× natif) : backend de corps wasm
  (limbs 32 bits ± SIMD128 ; build actuel SANS +simd128, ark-ff 0.5
  vanilla, wasm-opt -O4 web seulement — vérifier le blob node).

## #16 — Montgomery 32 bits wasm (fork youtpout/algebra) (2026-07-19)

Patch DÉPLACÉ du vendor/ (erreur : fork ~/Projects/algebra existait) vers
le fork : branche `wasm-mont-mul-32-v0.5` (tag v0.5.0 + patch, consommée
par [patch.crates-io] de proof-systems — TOUTE la famille ark doit venir
du même git sinon deux instances de traits) ; branche `wasm-mont-mul-32`
(master 0.6-pre + test différentiel local NoCarry255) = candidate PR
upstream arkworks. cfg(target_arch = "wasm32") = le « mot-clé de
compilation », chemin upstream intact ailleurs.
- Gain e2e : −5-8 % proves wasm (smokes dos-à-dos), bruit machine ±5-10 %
  du même ordre — voir BENCHMARKS.md. VK/preuves inchangées, gates verts.
- PIÈGES BUILD : (1) sans #[inline(always)] sur la routine, l'inlining
  LTO bascule ±10 % selon la provenance path/git des crates (sources
  identiques !) ; (2) codegen-units=1 : PIRE, reverté ; (3) l'addon natif
  mina_runtime se construit depuis le SUBMODULE o1js/src/mina-rust.
- Prochain (#17, demandé par eddy) : SIMD128 — flag seul d'abord (mesuré),
  micro-bench débit mul, puis noyau product-scanning i64x2.extmul sous
  cfg(target_feature = "simd128") dans la même branche. Arrêt si le
  micro-bench dit non-profitable (verdict à consigner).

## #17 — SIMD128 : NON-PROFITABLE, clos chiffres en main (2026-07-19)

Protocole en 3 étapes, arrêt au verdict (règle d'eddy) :
flag +simd128 seul = rien ; micro-bench champ : wasm 44 ns/mul vs natif
13,2 (3,3×), latence=débit ; sonde SIMD réelle (SOS extmul auto-vérifiée)
= 316 ns/mul, 7× PIRE. Cause : le scalaire wasm fait déjà 1 produit
32×32→64/instruction en registres ; la formulation SIMD paie splits
lo/hi + trafic mémoire colonnes pour un plafond ~15 %. NE PAS retenter
sous cette forme. Seule voie SIMD restante : batching vertical 2 lanes
(exige sites d'appel appariés MSM/FFT = chirurgie d'API, à coupler à la
représentation 29/30 bits si chantier lourd un jour).
Outil pérenne : rust_pickles_bench_field_mul(iters, mode) dans le blob.
Flag et sonde retirés (8b6cb0a689) ; tout consigné dans BENCHMARKS.md.

## Addendum #17 — batching vertical (restructuration des calculs) : NON aussi

Eddy a demandé la forme restructurée (2 muls indépendantes en lanes).
Sondes auto-vérifiées : verticale 387 ns/mul, déroulée main 184 ns/mul,
vs scalaire 44. PLANCHER mesuré : 2,7 ns par instruction v128 en chaîne
dépendante (~8-10 cycles) vs ~0,3 ns scalaire → parité au MIEUX, toutes
formulations exclues sur V8/x64 actuel. SIMD backend de corps = DOSSIER
CLOS (re-mesurer seulement si les moteurs changent ; sondes dans
l'historique git de kimchi-wasm/src/pickles.rs, outil bench modes 0/1
pérenne). Leviers restants à rendement documenté : restore pk ~1,1 s
(warm compile), analyzeMethods TS 442 ms, représentation 29/30 bits
(chantier lourd, seul espoir wasm >10 %).

## #18 — lazy-carry 29 bits : sonde GO (1,6× en débit) (2026-07-19)

Enfin un GO mesuré côté champ wasm : 9 limbs 29 bits, colonnes u64 sans
propagation de retenues (18 produits/colonne max, < 2^62,5). Sonde
pérenne = modes 6/7 de rust_pickles_bench_field_mul (1b10d392a4),
auto-vérifiée via domaine Montgomery 2^261 (PIÈGE : entrer/sortir par
into_bigint(), PAS .0.0 qui est la repr interne R64 ; DCE : black_box
obligatoire sur la boucle chronométrée).
Chiffres : latence 37,1 vs 42,8 ; DÉBIT 26,9 vs 42,5 ns/mul (−37 %).
Intégration à cadrer (PAS drop-in) : par kernel, conversion de tableaux
aux frontières — ordre : FFT (amortit log n:1) → Poseidon → MSM (ark-ec,
lourd). Chaque étape : sonde → intégration → protocole bench complet.

## #18 suite — fondation lazy29 dans le fork algebra (2026-07-19)

Module générique `ark_ff::lazy29` (fork youtpout/algebra, branches master
2505d565 + v0.5 d4672bdc) : mont_mul/add/sub sous invariant < 2p (pas de
réduction finale en chaîne), enter/exit sur la REPR INTERNE (.0, PAS
into_bigint — piège qui a mordu deux fois), entry_constant = 2^266 mod p
runtime, exit via mont_mul par R (const). Constantes 29 bits const fn
depuis MODULUS. Tests différentiels : chaînes mixtes 200 étapes sur bls
(fork) + les deux champs pasta (pickles). Bornes démontrées dans les
doc-comments (T < p/16 + p). Yrrid (1er prix ZPRIZE) = catalogue pour le
futur kernel MSM : GLV racine-cubique (pasta l'a), digits signés,
fenêtres 10-16, batch-affine Aztec ; code C non réutilisable tel quel.
PROCHAINE ÉTAPE : câbler la FFT d'ark-poly (fork) sur lazy29 sous
cfg(wasm32) — conversion des tableaux aux frontières, papillons en
domaine < 2p, sonde par taille de domaine PUIS protocole bench complet.

## #18 suite — sonde FFT lazy29 : GO (2026-07-19)

FFT radix-2 complète en domaine lazy29 (0f735f4c32, modes 8/9) :
**26,9 ms/fft SÉRIE (conversions incluses) vs 34,5 ms ark PARALLÈLE
16 workers à 2^16** — le kernel série bat déjà la prod. Prochaine étape
du chantier : l'INTÉGRATION — parallèle rayon par blocs (même découpage
qu'ark) + branchement dans le chemin FFT du prover. Point de plomberie
identifié : ark-poly est générique (T: DomainCoeff<F>) — la spécialisation
passe par un downcast TypeId T==F + un trait capability, OU par un shim
côté kimchi (types concrets pasta, bound ajoutable). Trancher au moment
de l'implémentation. PIÈGES session : (1) TOUJOURS cp le blob vers
dist/node après build:wasm:node:rust (un blob périmé dans dist a fait
tomber les modes 8/9 dans le bras _ ⇒ mesures fantômes 0 ms) ;
(2) ark-poly feature parallel ⇒ fft DOIT tourner dans run_in_pool ;
(3) sonde via o1js dist : exporter rustPicklesBindings temporairement et
lancer depuis dist/node (chemins cwd-relatifs du loader jsoo).

## #18 FFT — CORRECTION du GO + verdict final : NO-GO du dispatch (2026-07-19)

DÉCOUVERTE CRITIQUE : le harnais de sonde (rustPicklesBindings appelé
directement) tournait avec un pool rayon à **1 THREAD** — la prod passe
par withThreadPool (bindings.js) qui initialise numWorkers =
availableParallelism-1. Les « 34,5 ms ark PARALLÈLE 16 workers » du GO
précédent étaient de l'ark SÉRIE. Règle : toute sonde perf doit tourner
DANS withThreadPool et vérifier rayon::current_num_threads() (mode 11,
iters=0 → nb threads ; région parallèle vide ≈ 3-4 µs, jamais le goulot).

L'intégration a été menée au bout puis mesurée honnêtement : dispatch
générique dans le fork ark-poly (radix2::lazy, entonnoir io/oi_helper,
downcast T==F via TypeId — DomainCoeff gagne 'static —, sonde runtime
repr(1)==R/repr(2)==2R depuis characteristic() seul, Params runtime dans
ff::lazy29 dérivés du module), réseaux de papillons et découpage
parallèle identiques à ark, racines contiguës par étage, stockage u32
36 B/élément. Correction PROUVÉE (tests différentiels natifs + A/B
auto-vérifié dans le blob). Perf, pool réel (V8/x64, 16c/32t) :

threads:      2      4      8      15     31    (ms/fft 2^16)
lazy:      18,4    9,7    7,9    6,0    7,1
ark:       17,8    9,8    6,7    5,5    5,2
(2^12 : ark gagne partout aussi ; à 1 thread le chemin intégré fait
37 ms — les surcoûts par appel mangent même l'avantage série)

CAUSE DE FOND (à retenir pour les prochains kernels) : la FFT a une
intensité arithmétique très faible (1 mul par paire d'éléments par
étage). Parallélisée, elle est bornée par le système mémoire, pas par
les multiplications : l'avantage de débit mul du lazy29 (26,9 vs
42,5 ns/mul, réel) s'évapore, et les conversions aux frontières
(~2,5n muls) + racines par appel restent en pur surcoût. Le u32-packing
(2,25× → 1,12× le trafic d'ark) n'a rien changé — pas la bande passante
brute, le niveau caches/latence. L'ark 32 bits borné latence profite en
plus du SMT.

DÉCISION : dispatch DEFAULT OFF derrière ark_poly set_wasm_lazy_fft
(kill-switch runtime, binding wasm rust_pickles_set_lazy_fft) — la prod
= ark inchangé ; la plomberie complète reste testée (tests différentiels
sur master du fork) et mesurable en A/B un-seul-blob (modes 8/13 avec
bascule). Réactivable si un hôte à pool étroit le justifie un jour.

CE QUI RESTE VALIDE de #18 : le kernel mul lazy29 (1,6× débit, modes
6/7) et le module ff::lazy29 (+ Params runtime). Cibles où l'avantage
survit au parallélisme = kernels à FORTE intensité arithmétique :
1) POSEIDON (chaînes mul/square séquentielles par permutation, état de
3 éléments en registres, zéro inflation mémoire, le gain par op tient) ;
2) MSM (add de groupe ≈ 12 muls sur 3-4 éléments, compute-bound même
large ; recette Yrrid : GLV, digits signés, batch-affine).
Sondes : fft-probe3/fft-crossover.mjs (scratchpad session) — schéma :
import withThreadPool + setNumberOfWorkers AVANT rustPicklesBindings.

## Recensement kernels (2026-07-19) — Poseidon abandonné, cap sur MSM (#20)

Compteurs wasm (fork ec/poly + mina-poseidon, binding
rust_pickles_kernel_census) sur le bench chaud rust-wasm complet :
Poseidon 7 594 permutations ≈ 0,42 s (~2,5 % — kernel SANS intérêt e2e,
verdict mesuré, mode 15 = 56 µs/permutation) ; MSM 500 appels /
3,80 M points (~35 %) ; FFT 584 appels / 33,6 M éléments (~25 %,
lazy exclu). #20 = kernel MSM dans le fork ark-ec sous cfg(wasm32) :
GLV racine-cubique (pasta), digits signés, batch-affine (Aztec) ;
lazy29 pour les coordonnées seulement si l'intensité arithmétique le
justifie (leçon FFT : parallèle + faible intensité ⇒ borné mémoire).
Piste FFT classique restante : cache de racines par domaine
(~17 M muls/run recalculées). Sonde baseline MSM = mode 16.

## #20 — sonde baseline MSM posée (2026-07-19)

Mode 16 (iters = log2 n, Vesta/Fp, self-check somme naïve, run_in_pool) :
2751/2103/1602 ns/point à 2^12/2^14/2^16, pool 31 threads. ark 0.5 fait
DÉJÀ wnaf signé (msm_bigint_wnaf via NEGATION_IS_CHEAP). Chantier v1 =
batch-affine buckets sous cfg(wasm32) dans le fork ark-ec (inversion
amortie Montgomery-batch, ordonnanceur anti-collision — cœur de la
recette Yrrid/Mitscha-Baude) ; v2 = GLV (impl GLVConfig pour pasta dans
mina-curves : endo racine cubique, décomposition lattice). Rappel pièges :
sondes DANS withThreadPool ; cp blob vers dist/node après build ;
export temporaire rustPicklesBindings restauré (.bak) après usage.

## #20 — MSM batch-affine : kernel −17,5 %, e2e −3 à −5 % proves wasm (2026-07-19)

Kernel dans le fork ark-ec (batch_affine.rs) : arbres par bucket,
additions affines, une inversion batch par niveau, cas dégénérés
classifiés (tests différentiels auto-contenus sur master — corps local +
courbe y²=x³+3 germée en (1,2), COEFF_B placebo car les formules a=0 ne
le lisent pas). PIÈGES : dernier digit wnaf non recentré ⇒ 2^c buckets
pleins ; v1 perdait tout dans la matérialisation des paires (~160 o/add)
— in-place sûr par ordre des paires ; petites tailles dominées par le
verrou dlmalloc ⇒ scratch par thread (map_init). Crossover : 2^13 +6 %,
2^14 −13 %, 2^16 −17,5 % ⇒ seuil 2^14, override SW msm_bigint
cfg(wasm32), interrupteur set_wasm_batch_affine_msm (défaut ON).
Census v2 (classes de taille) : 67 % des points au-dessus du seuil.
E2E : proves rust-wasm 3428/4494/5800 (−3 à −5 %), gates verts.
SUITE : GLV (constantes d'endo pasta dans mina-curves, GLVConfig),
fenêtres adaptées au coût affine. Rappel : cargo update après CHAQUE
push du fork (une fois il a silencieusement gardé l'ancien rev — tail
la sortie, vérifier le rev dans Cargo.lock).

## Recensement v3 — chronos de phase (2026-07-19)

live_trace gagne set_clock/take_phase_times (intervalle attribué au
checkpoint OUVRANT ; `_done` ferme sans ouvrir) ; census expose
"phases". Run chaud rust-wasm : IPA 2,84 s / QUOTIENT 2,51 s / commits
témoins 1,73 s / witness gen 1,23 s / FFT témoins 0,55 s (sur ~9,8 s
instrumentées, ~4,3 s hors chronos — wrap sous-instrumenté, 4 counts
pour 3 proves : à éclaircir). STEERING : 1) quotient en lazy29 (profil
idéal : forte intensité, tableaux d8, conversions amorties sur des
dizaines d'ops/élément) ; 2) GLV ; 3) décomposer create_aggregated_ipa
(folding vectoriel vs MSMs). Roots-cache FFT rétrogradé (0,55 s
visibles).

## #22 — backend rust-wasm en NAVIGATEUR : opérationnel (2026-07-19)

o1js : build:wasm:web:rust (make build-web de proof-systems, target web,
blob commun caml_*+rust_pickles_* comme node) ; build-web.js stubbe les
imports node du bundle web (PIÈGES : esbuild inline les imports
dynamiques EAGERLY → le top-level de native.js exécute createRequire →
le stub doit RETOURNER une fonction qui ne lève qu'à l'appel ;
node:fs/node:module en scheme non géré par webpack → stubs esbuild, pas
external) ; web-backend.js : mémoire initiale 20→32 pages (blob rust en
déclare 24). UIs : zkapp-rust/ui-rust (3010) + ui-jsoo (3020, npm
2.15.0), même code, workers comlink, COOP/COEP. RÉSULTAT : chaîne
récursive complète en navigateur — compile 17,1 s, init 6,0 s, update
7,5 s, merge 9,3 s, VK == npm 2.15 (10959…5723), 5+6=11 ✓. jsoo npm :
update BLOQUÉ >8 min dans le Chromium embarqué (récursion ; retester
Chrome normal). Autres pièges : cache .next rassis après changement de
dist (rm -rf .next + restart) ; pkill -f matche sa propre commande
(fuser -k PORT/tcp) ; les 43 Mo de chunk worker = dev non minifié.
