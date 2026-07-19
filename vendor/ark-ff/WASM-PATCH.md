# ark-ff 0.5.0 vendored — patch wasm

Source : copie exacte de crates.io `ark-ff-0.5.0`, branchée par
`[patch.crates-io]` dans le Cargo.toml du workspace.

## Modification unique

`src/fields/models/fp/montgomery_backend.rs` :

- `mul_assign_u32_digits` — la même CIOS « no-carry » que le chemin
  générique 64 bits, en digits de 32 bits. wasm32 a une multiplication
  native 32×32→64 (`i64.mul`) mais émule chaque produit 64×64→128 du
  chemin 64 bits. La représentation `[u64; N]` ne change pas (split/join
  aux frontières de la routine) : layout, sérialisation et constantes
  identiques, résultats bit-identiques.
- Dispatch dans `mul_assign` : uniquement `cfg!(target_arch = "wasm32")`
  et dans la branche `CAN_USE_NO_CARRY_MUL_OPT` (la condition 64 bits
  teste exactement le même bit de poids fort, donc la garantie no-carry
  vaut aussi en digits 32 bits). Les cibles natives compilent le code
  upstream inchangé.

## Garde-fous

- La routine est compilée sur toutes les cibles (dispatch wasm seulement)
  pour permettre le test différentiel NATIF :
  `pickles/src/common.rs::wasm_mont_mul_32_matches_64bit_path`
  (32 bits vs 64 bits sur Fp et Fq pasta, chaînes de carrés + 0/1/-1).
- `debug_assert` sur la retenue finale (condition no-carry).
- Les gates e2e (VkParity 3/3, preuves vérifiées) valident l'identité
  des résultats sur les vrais circuits.

## Mise à jour

Pour monter de version ark-ff : re-copier la nouvelle version depuis le
registry, ré-appliquer ce patch (une routine + un dispatch), re-runner le
test différentiel puis le protocole bench (BENCHMARKS.md dans zkapp-rust).
