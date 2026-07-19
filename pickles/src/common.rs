//! Common constants and helpers (port of pickles' `common.ml`).

use crate::composition_types::ProofsVerified;
use mina_curves::pasta::{Pallas, Vesta};
use poly_commitment::{ipa::SRS, SRS as _};
use std::sync::{Arc, OnceLock};

/// The maximum number of previous proofs a step circuit can verify.
/// (OCaml: `Nat.N2` — pickles is specialized to width 2.)
pub const MAX_PROOFS_VERIFIED: usize = 2;

/// The number of bits used for scalar challenges.
/// (OCaml: `Challenge.Constant.length = 128`.)
pub const SCALAR_CHALLENGE_BITS: usize = 128;

/// The number of rounds of the IPA on the Tick (step / Vesta) side —
/// log2 of the maximum domain size.
pub const TICK_ROUNDS: usize = 16;

/// The number of rounds of the IPA on the Tock (wrap / Pallas) side.
pub const TOCK_ROUNDS: usize = 15;

/// Returns Mina's full Tick SRS.
///
/// `SnarkyCircuit` passes the circuit domain size here. That domain can be
/// smaller than Mina's fixed proof SRS (for example the 512-row base Step
/// circuit), so it must not be used as the SRS size or asserted to equal it.
static TICK_SRS: OnceLock<Arc<SRS<Vesta>>> = OnceLock::new();
static TOCK_SRS: OnceLock<Arc<SRS<Pallas>>> = OnceLock::new();

pub fn tick_srs(_domain_size: usize) -> Arc<SRS<Vesta>> {
    // wasm32: the ~1<<16 serial group maps dominate the first compile, and the
    // one compile call sits alone in the worker pool, so parallel creation is
    // a pure win. Native keeps the serial create: many tests hit this
    // `OnceLock` from inside rayon pools concurrently, and a parallel
    // initializer behind a blocking `get_or_init` starves the pool.
    #[cfg(target_arch = "wasm32")]
    let create = || Arc::new(SRS::<Vesta>::create_parallel(1 << TICK_ROUNDS));
    #[cfg(not(target_arch = "wasm32"))]
    let create = || Arc::new(SRS::<Vesta>::create(1 << TICK_ROUNDS));
    TICK_SRS.get_or_init(create).clone()
}

/// Returns Mina's full Tock SRS independently of the circuit domain size.
pub fn tock_srs(_domain_size: usize) -> Arc<SRS<Pallas>> {
    // See `tick_srs` for the wasm32/native split rationale.
    #[cfg(target_arch = "wasm32")]
    let create = || Arc::new(SRS::<Pallas>::create_parallel(1 << TOCK_ROUNDS));
    #[cfg(not(target_arch = "wasm32"))]
    let create = || Arc::new(SRS::<Pallas>::create(1 << TOCK_ROUNDS));
    TOCK_SRS.get_or_init(create).clone()
}

/// Raw SRS cache format: `SRS2` magic, u64-LE point count, the blinding
/// point `h`, then the `g` vector — uncompressed, unvalidated points (the
/// jsoo-parity disk cache: jsoo persists its SRS too).
pub const SRS_RAW_MAGIC: [u8; 4] = *b"SRS2";

fn encode_srs_raw<G>(g: &[G], h: &G) -> Option<Vec<u8>>
where
    G: ark_serialize::CanonicalSerialize,
{
    let point_size = h.uncompressed_size();
    let mut out = Vec::with_capacity(12 + (g.len() + 1) * point_size);
    out.extend_from_slice(&SRS_RAW_MAGIC);
    out.extend_from_slice(&(g.len() as u64).to_le_bytes());
    h.serialize_uncompressed(&mut out).ok()?;
    for point in g {
        point.serialize_uncompressed(&mut out).ok()?;
    }
    Some(out)
}

fn decode_srs_raw<G>(bytes: &[u8]) -> Option<(Vec<G>, G)>
where
    G: ark_serialize::CanonicalDeserialize + Send,
{
    use rayon::prelude::*;
    if bytes.len() < 12 || bytes[..4] != SRS_RAW_MAGIC {
        return None;
    }
    let count = u64::from_le_bytes(bytes[4..12].try_into().ok()?) as usize;
    let body = &bytes[12..];
    if count == 0 || body.is_empty() || body.len() % (count + 1) != 0 {
        return None;
    }
    let point_size = body.len() / (count + 1);
    let h = G::deserialize_uncompressed_unchecked(&body[..point_size]).ok()?;
    let g: Option<Vec<G>> = body[point_size..]
        .par_chunks_exact(point_size)
        .map(|chunk| G::deserialize_uncompressed_unchecked(chunk).ok())
        .collect();
    Some((g?, h))
}

/// Seeds the process-global Tick SRS from a raw cache payload. Returns
/// `false` (and leaves any existing SRS untouched) on a malformed payload.
pub fn seed_tick_srs_raw(bytes: &[u8]) -> bool {
    if TICK_SRS.get().is_some() {
        return true;
    }
    match decode_srs_raw::<Vesta>(bytes) {
        Some((g, h)) if g.len() == 1 << TICK_ROUNDS => {
            let _ = TICK_SRS.set(Arc::new(SRS::new(g, h)));
            true
        }
        _ => false,
    }
}

/// Seeds the process-global Tock SRS from a raw cache payload.
pub fn seed_tock_srs_raw(bytes: &[u8]) -> bool {
    if TOCK_SRS.get().is_some() {
        return true;
    }
    match decode_srs_raw::<Pallas>(bytes) {
        Some((g, h)) if g.len() == 1 << TOCK_ROUNDS => {
            let _ = TOCK_SRS.set(Arc::new(SRS::new(g, h)));
            true
        }
        _ => false,
    }
}

/// Exports the Tick SRS raw cache payload, when the SRS exists.
pub fn export_tick_srs_raw() -> Option<Vec<u8>> {
    let srs = TICK_SRS.get()?;
    encode_srs_raw(&srs.g, &srs.h)
}

/// Exports the Tock SRS raw cache payload, when the SRS exists.
pub fn export_tock_srs_raw() -> Option<Vec<u8>> {
    let srs = TOCK_SRS.get()?;
    encode_srs_raw(&srs.g, &srs.h)
}

// ---------------------------------------------------------------------------
// jsoo-format cache payloads (o1js `Cache` entries, shared with jsoo)
// ---------------------------------------------------------------------------
//
// o1js persists the SRS and Lagrange bases through its `Cache` object using
// JSON payloads (`OrInfinityJson` points with decimal coordinates). The rust
// backends read and write those exact entries — `srs-fp-65536`,
// `srs-fq-32768`, `lagrange-basis-{f}-{domain}` — so a cache warmed by jsoo
// warms rust and vice versa, and the o1js gating (`Cache.None`, `canWrite`)
// applies identically to both.

/// One point in o1js's jsoo cache JSON: `"Infinity"` or `{x, y}` with
/// decimal-string coordinates.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
enum JsooPointJson {
    Infinity(String),
    Point { x: String, y: String },
}

/// Parses a decimal string into a field element without heap allocation.
/// wasm's allocator takes a single global lock, so `BigUint`-based parsing
/// SERIALIZES across the worker pool (measured: parallel decode 3x slower
/// than serial); stack-only limb arithmetic keeps the fan-out real.
/// Returns `None` on empty input, invalid digits, or values >= the modulus.
fn field_from_decimal<F: ark_ff::PrimeField>(s: &str) -> Option<F> {
    if s.is_empty() {
        return None;
    }
    let mut limbs = F::BigInt::default();
    for byte in s.bytes() {
        let digit = byte.wrapping_sub(b'0');
        if digit > 9 {
            return None;
        }
        // limbs = limbs * 10 + digit, rejecting overflow past the top limb.
        let mut carry = digit as u128;
        for limb in limbs.as_mut() {
            let value = (*limb as u128) * 10 + carry;
            *limb = value as u64;
            carry = value >> 64;
        }
        if carry != 0 {
            return None;
        }
    }
    F::from_bigint(limbs)
}

fn point_from_jsoo<G>(point: &JsooPointJson) -> Option<G>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    match point {
        JsooPointJson::Infinity(tag) => (tag == "Infinity").then(G::zero),
        JsooPointJson::Point { x, y } => {
            let x = field_from_decimal::<G::BaseField>(x)?;
            let y = field_from_decimal::<G::BaseField>(y)?;
            // Trusted local cache state: points load unvalidated, like jsoo's.
            Some(G::of_coordinates(x, y))
        }
    }
}

fn point_to_jsoo<G>(point: &G) -> JsooPointJson
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    use ark_ff::PrimeField as _;
    match point.to_coordinates() {
        None => JsooPointJson::Infinity("Infinity".into()),
        Some((x, y)) => JsooPointJson::Point {
            x: x.into_bigint().to_string(),
            y: y.into_bigint().to_string(),
        },
    }
}

fn decode_srs_jsoo<G>(bytes: &[u8]) -> Option<(Vec<G>, G)>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    use rayon::prelude::*;
    // jsoo's `caml_srs_get` payload: `[h, ...g]`. The JSON parse is fast;
    // the decimal-string -> field conversions dominate, so they run in
    // parallel (the wasm host seeds inside the worker pool).
    let points: Vec<JsooPointJson> = serde_json::from_slice(bytes).ok()?;
    let (h_point, g_points) = points.split_first()?;
    let h = point_from_jsoo(h_point)?;
    let g: Option<Vec<G>> = g_points.par_iter().map(point_from_jsoo).collect();
    Some((g?, h))
}

fn encode_srs_jsoo<G>(g: &[G], h: &G) -> Option<Vec<u8>>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    let mut points = Vec::with_capacity(g.len() + 1);
    points.push(point_to_jsoo(h));
    points.extend(g.iter().map(point_to_jsoo));
    serde_json::to_vec(&points).ok()
}

/// Seeds the process-global Tick SRS from a jsoo cache payload (`[h, ...g]`
/// JSON). Returns `false` (leaving any existing SRS untouched) on a malformed
/// or wrong-size payload.
pub fn seed_tick_srs_jsoo(bytes: &[u8]) -> bool {
    if TICK_SRS.get().is_some() {
        return true;
    }
    match decode_srs_jsoo::<Vesta>(bytes) {
        Some((g, h)) if g.len() == 1 << TICK_ROUNDS => {
            let _ = TICK_SRS.set(Arc::new(SRS::new(g, h)));
            true
        }
        _ => false,
    }
}

/// Seeds the process-global Tock SRS from a jsoo cache payload.
pub fn seed_tock_srs_jsoo(bytes: &[u8]) -> bool {
    if TOCK_SRS.get().is_some() {
        return true;
    }
    match decode_srs_jsoo::<Pallas>(bytes) {
        Some((g, h)) if g.len() == 1 << TOCK_ROUNDS => {
            let _ = TOCK_SRS.set(Arc::new(SRS::new(g, h)));
            true
        }
        _ => false,
    }
}

/// Exports the Tick SRS as the jsoo cache payload, when the SRS exists.
pub fn export_tick_srs_jsoo() -> Option<Vec<u8>> {
    let srs = TICK_SRS.get()?;
    encode_srs_jsoo(&srs.g, &srs.h)
}

/// Exports the Tock SRS as the jsoo cache payload, when the SRS exists.
pub fn export_tock_srs_jsoo() -> Option<Vec<u8>> {
    let srs = TOCK_SRS.get()?;
    encode_srs_jsoo(&srs.g, &srs.h)
}

/// One commitment in o1js's jsoo Lagrange cache JSON. The single-chunk
/// commitment lives under the (historically misnamed) `shifted` key.
#[derive(serde::Serialize, serde::Deserialize)]
struct JsooCommJson {
    shifted: Vec<JsooPointJson>,
}

/// Decodes a jsoo Lagrange-basis cache payload; `None` on any shape mismatch.
pub fn decode_lagrange_basis_jsoo<G>(
    bytes: &[u8],
    expected_len: usize,
) -> Option<Vec<poly_commitment::commitment::PolyComm<G>>>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    use rayon::prelude::*;
    let comms: Vec<JsooCommJson> = serde_json::from_slice(bytes).ok()?;
    if comms.len() != expected_len {
        return None;
    }
    comms
        .par_iter()
        .map(|comm| {
            let chunks: Option<Vec<G>> = comm.shifted.iter().map(point_from_jsoo).collect();
            Some(poly_commitment::commitment::PolyComm { chunks: chunks? })
        })
        .collect()
}

/// Encodes a Lagrange basis as the jsoo cache payload.
pub fn encode_lagrange_basis_jsoo<G>(
    basis: &[poly_commitment::commitment::PolyComm<G>],
) -> Option<Vec<u8>>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G::BaseField: ark_ff::PrimeField,
{
    let comms: Vec<JsooCommJson> = basis
        .iter()
        .map(|comm| JsooCommJson {
            shifted: comm.chunks.iter().map(point_to_jsoo).collect(),
        })
        .collect();
    serde_json::to_vec(&comms).ok()
}

/// Seeds the in-memory Lagrange-basis cache for `curve` ("vesta"/"pallas")
/// and `2^domain_log2` from a jsoo cache payload. Returns `false` on any
/// mismatch (the basis is then recomputed on demand).
pub fn seed_lagrange_basis_jsoo(curve: &str, domain_log2: u32, bytes: &[u8]) -> bool {
    let domain_size = 1usize << domain_log2;
    match curve {
        "vesta" => {
            let Some(basis) = decode_lagrange_basis_jsoo::<Vesta>(bytes, domain_size) else {
                return false;
            };
            tick_srs(1 << TICK_ROUNDS)
                .lagrange_bases()
                .set_once(domain_size, basis);
            true
        }
        "pallas" => {
            let Some(basis) = decode_lagrange_basis_jsoo::<Pallas>(bytes, domain_size) else {
                return false;
            };
            tock_srs(1 << TOCK_ROUNDS)
                .lagrange_bases()
                .set_once(domain_size, basis);
            true
        }
        _ => false,
    }
}

/// Exports a computed Lagrange basis as the jsoo cache payload; `None` when
/// the basis is not (yet) in the in-memory cache.
pub fn export_lagrange_basis_jsoo(curve: &str, domain_log2: u32) -> Option<Vec<u8>> {
    let domain_size = 1usize << domain_log2;
    fn export<G>(srs: &SRS<G>, domain_size: usize) -> Option<Vec<u8>>
    where
        G: poly_commitment::commitment::CommitmentCurve,
        G::BaseField: ark_ff::PrimeField,
    {
        if !srs.lagrange_bases().contains_key(&domain_size) {
            return None;
        }
        let basis = srs
            .lagrange_bases()
            .get_or_generate(domain_size, || unreachable!("checked contains_key"));
        encode_lagrange_basis_jsoo(&basis)
    }
    match curve {
        "vesta" => export(&tick_srs(1 << TICK_ROUNDS), domain_size),
        "pallas" => export(&tock_srs(1 << TOCK_ROUNDS), domain_size),
        _ => None,
    }
}

/// The Poseidon full-rounds constant shared with the snarky crate.
pub const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;

/// The default number of commitment chunks (`Plonk_checks.num_chunks_by_default`);
/// the base step/wrap circuits use a single chunk per column.
pub const NUM_CHUNKS_BY_DEFAULT: usize = 1;

/// The log2 domain size of the wrap circuit as a function of the number of
/// proofs it verifies (`Common.wrap_domains`): `0 -> 13`, `1 -> 14`, `2 -> 15`.
///
/// # Panics
/// Panics if `proofs_verified > 2` (pickles is specialized to width ≤ 2).
pub fn wrap_domain_log2(proofs_verified: usize) -> u32 {
    match proofs_verified {
        0 => 13,
        1 => 14,
        2 => 15,
        _ => panic!("wrap_domain_log2: proofs_verified must be 0, 1 or 2"),
    }
}

/// Inverse of [`wrap_domain_log2`] (`Common.actual_wrap_domain_size`): recovers
/// the number of proofs verified by a padded wrap circuit domain.
///
/// # Panics
/// Panics if `log2_domain_size` is not one of 13, 14 or 15.
pub fn actual_wrap_domain_size(log2_domain_size: u32) -> ProofsVerified {
    match log2_domain_size {
        13 => ProofsVerified::N0,
        14 => ProofsVerified::N1,
        15 => ProofsVerified::N2,
        _ => panic!("actual_wrap_domain_size: log2 domain size must be 13, 14 or 15"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `wrap_domain_log2` reproduces `Common.wrap_domains` (common.ml).
    #[test]
    fn wrap_domain_log2_matches_ocaml() {
        assert_eq!(wrap_domain_log2(0), 13);
        assert_eq!(wrap_domain_log2(1), 14);
        assert_eq!(wrap_domain_log2(2), 15);
    }

    #[test]
    #[should_panic(expected = "proofs_verified must be 0, 1 or 2")]
    fn wrap_domain_log2_rejects_width_3() {
        let _ = wrap_domain_log2(3);
    }

    /// The jsoo SRS/Lagrange payload codecs round-trip, and the JSON matches
    /// the o1js shape (`[h, ...g]` decimal points, `{"shifted": [...]}`
    /// commitments) so entries are interchangeable with jsoo's.
    #[test]
    fn jsoo_cache_payloads_round_trip() {
        let tiny = SRS::<Vesta>::create(4);
        let (g, h) = (tiny.g.clone(), tiny.h);
        let bytes = encode_srs_jsoo(&g, &h).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json.as_array().unwrap().len(), 5);
        assert!(json[0]["x"].as_str().unwrap().parse::<num_bigint::BigUint>().is_ok());
        let (g2, h2) = decode_srs_jsoo::<Vesta>(&bytes).unwrap();
        assert_eq!(g, g2);
        assert_eq!(h, h2);

        let basis: Vec<poly_commitment::commitment::PolyComm<Vesta>> = g
            .iter()
            .map(|p| poly_commitment::commitment::PolyComm { chunks: vec![*p] })
            .collect();
        let bytes = encode_lagrange_basis_jsoo(&basis).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert!(json[0]["shifted"].is_array());
        let basis2 = decode_lagrange_basis_jsoo::<Vesta>(&bytes, 4).unwrap();
        assert_eq!(basis, basis2);
        assert!(decode_lagrange_basis_jsoo::<Vesta>(&bytes, 5).is_none());
    }

    /// `actual_wrap_domain_size` reproduces `Common.actual_wrap_domain_size`.
    #[test]
    fn actual_wrap_domain_size_matches_ocaml() {
        assert_eq!(actual_wrap_domain_size(13), ProofsVerified::N0);
        assert_eq!(actual_wrap_domain_size(14), ProofsVerified::N1);
        assert_eq!(actual_wrap_domain_size(15), ProofsVerified::N2);
    }

    #[test]
    #[should_panic(expected = "log2 domain size must be 13, 14 or 15")]
    fn actual_wrap_domain_size_rejects_other_domains() {
        let _ = actual_wrap_domain_size(12);
    }
}

/// Warms the process-wide SRS and Lagrange-basis caches in parallel.
///
/// jsoo loads precomputed SRS/Lagrange data from disk; computing them lazily
/// inside the first compile serializes ~1s of SRS hashing per curve plus
/// 0.3-1.9s of group-IFFT per domain on the critical path. The recursion
/// domains are architecture constants, so warm them all concurrently up
/// front — loading each Lagrange basis from the on-disk cache when present
/// (`PICKLES_CACHE_DIR`, default `$XDG_CACHE_HOME/pickles-rs`), computing and
/// persisting it otherwise.
pub fn warm_recursion_caches(recursive: bool) {
    use rayon::prelude::*;
    let tick_domains: &[u32] = if recursive { &[14, 15, 16] } else { &[] };
    let tock_domains: &[u32] = if recursive { &[13, 15] } else { &[13] };
    rayon::join(
        || {
            let srs = tick_srs(1 << TICK_ROUNDS);
            tick_domains
                .par_iter()
                .for_each(|&log2| lagrange_from_cache_or_compute(&srs, "vesta", log2));
        },
        || {
            let srs = tock_srs(1 << TOCK_ROUNDS);
            tock_domains
                .par_iter()
                .for_each(|&log2| lagrange_from_cache_or_compute(&srs, "pallas", log2));
        },
    );
}

/// Magic prefix of the raw (v2) Lagrange-basis cache format.
pub const LAGRANGE_RAW_MAGIC: [u8; 4] = *b"LGB2";

/// Encodes a Lagrange basis in the raw v2 cache format: `LGB2` magic, u64-LE
/// commitment count, then one uncompressed point per single-chunk commitment.
/// The serde (v1) format stores compressed validated points, which spends a
/// square root per point at load time; raw bytes make seeding IO-bound. The
/// cache directory is trusted local state, exactly like the v1 files.
/// Returns `None` for chunked commitments (not a Lagrange basis shape).
pub fn encode_lagrange_basis_raw<G>(
    basis: &[poly_commitment::commitment::PolyComm<G>],
) -> Option<Vec<u8>>
where
    G: ark_serialize::CanonicalSerialize,
{
    let first = basis.first()?;
    if first.chunks.len() != 1 {
        return None;
    }
    let point_size = first.chunks[0].uncompressed_size();
    let mut out = Vec::with_capacity(12 + basis.len() * point_size);
    out.extend_from_slice(&LAGRANGE_RAW_MAGIC);
    out.extend_from_slice(&(basis.len() as u64).to_le_bytes());
    for comm in basis {
        if comm.chunks.len() != 1 {
            return None;
        }
        comm.chunks[0].serialize_uncompressed(&mut out).ok()?;
    }
    Some(out)
}

/// Decodes the raw v2 Lagrange-basis cache format (see
/// [`encode_lagrange_basis_raw`]), deserializing the points unvalidated and in
/// parallel. Returns `None` on any shape mismatch.
pub fn decode_lagrange_basis_raw<G>(
    bytes: &[u8],
    expected_len: usize,
) -> Option<Vec<poly_commitment::commitment::PolyComm<G>>>
where
    G: ark_serialize::CanonicalDeserialize + Send + Sync,
{
    use rayon::prelude::*;
    let rest = bytes.strip_prefix(&LAGRANGE_RAW_MAGIC)?;
    let (count_bytes, points) = rest.split_at_checked(8)?;
    let count = u64::from_le_bytes(count_bytes.try_into().ok()?) as usize;
    if count != expected_len || count == 0 || points.len() % count != 0 {
        return None;
    }
    let point_size = points.len() / count;
    if point_size == 0 {
        return None;
    }
    points
        .par_chunks_exact(point_size)
        .map(|chunk| {
            G::deserialize_uncompressed_unchecked(chunk)
                .ok()
                .map(|point| poly_commitment::commitment::PolyComm {
                    chunks: vec![point],
                })
        })
        .collect()
}

/// Extension for exporting a cached Lagrange basis as raw v2 bytes (the wasm
/// host persists them since wasm itself has no filesystem).
pub trait LagrangeBasisExport {
    fn cached_lagrange_basis_bytes(&self, domain_size: usize) -> Vec<u8>;
}

impl<G> LagrangeBasisExport for SRS<G>
where
    G: poly_commitment::commitment::CommitmentCurve,
    G: ark_serialize::CanonicalSerialize + ark_serialize::CanonicalDeserialize,
{
    fn cached_lagrange_basis_bytes(&self, domain_size: usize) -> Vec<u8> {
        if !self.lagrange_bases().contains_key(&domain_size) {
            return Vec::new();
        }
        let basis = self
            .lagrange_bases()
            .get_or_generate(domain_size, || unreachable!("checked contains_key"));
        encode_lagrange_basis_raw(&basis).unwrap_or_default()
    }
}

/// Whether the crate-internal disk cache (`cache_dir`) is active. Hosts that
/// drive persistence through their own cache — o1js routes SRS/Lagrange
/// payloads through its `Cache` object, gated by `Cache.None`/`canWrite`
/// exactly like jsoo — disable it so no un-gated filesystem access remains.
/// Defaults to enabled for standalone (cargo test/CLI) use.
static DISK_CACHE_ENABLED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

/// Enables or disables the crate-internal SRS/Lagrange disk cache.
pub fn set_disk_cache_enabled(enabled: bool) {
    DISK_CACHE_ENABLED.store(enabled, std::sync::atomic::Ordering::Relaxed);
}

fn cache_dir() -> Option<std::path::PathBuf> {
    if !DISK_CACHE_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        return None;
    }
    if let Some(dir) = std::env::var_os("PICKLES_CACHE_DIR") {
        return Some(std::path::PathBuf::from(dir));
    }
    if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME") {
        return Some(std::path::PathBuf::from(xdg).join("pickles-rs"));
    }
    std::env::var_os("HOME").map(|home| {
        std::path::PathBuf::from(home)
            .join(".cache")
            .join("pickles-rs")
    })
}

/// Loads the Lagrange basis for `2^domain_log2` from the disk cache into the
/// SRS's in-memory cache, or computes it and persists it. Corrupt or absent
/// cache files only cost a recomputation.
fn lagrange_from_cache_or_compute<G>(srs: &SRS<G>, curve: &str, domain_log2: u32)
where
    G: poly_commitment::commitment::CommitmentCurve,
    G: ark_serialize::CanonicalSerialize + ark_serialize::CanonicalDeserialize,
    poly_commitment::ipa::SRS<G>: poly_commitment::SRS<G>,
{
    use ark_poly::EvaluationDomain as _;
    use poly_commitment::SRS as _;
    let domain_size = 1usize << domain_log2;
    let path = cache_dir().map(|dir| {
        dir.join(format!(
            "lagrange-{curve}-srs{}-d{domain_log2}.v2.bin",
            srs.g.len()
        ))
    });
    if let Some(path) = &path {
        if let Ok(bytes) = std::fs::read(path) {
            if let Some(basis) = decode_lagrange_basis_raw::<G>(&bytes, domain_size) {
                srs.lagrange_bases().set_once(domain_size, basis);
                return;
            }
        }
    }
    let domain =
        ark_poly::Radix2EvaluationDomain::<G::ScalarField>::new(domain_size).expect("domain");
    let basis: Vec<poly_commitment::commitment::PolyComm<G>> =
        srs.get_lagrange_basis(domain).clone();
    if let Some(path) = &path {
        if let Some(bytes) = encode_lagrange_basis_raw(&basis) {
            if let Some(parent) = path.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            // Write atomically enough: temp file + rename.
            let tmp = path.with_extension("tmp");
            if std::fs::write(&tmp, bytes).is_ok() {
                let _ = std::fs::rename(&tmp, path);
            }
        }
    }
}
