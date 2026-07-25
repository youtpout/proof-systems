//! Montgomery multiplication for the Pasta fields on aarch64.
//!
//! `ark-ff` only ships assembly carry chains for x86_64: every other target,
//! phones and browsers included, falls back to portable Rust, where each
//! 64x64 product has its carry materialised through a 128-bit temporary. A
//! Mina proof is bound by this multiplication -- the IPA base folding alone is
//! a quarter of a mobile proving run -- so the carry chains are worth writing
//! out.
//!
//! The algorithm is the one `ark-ff` uses for these moduli, CIOS with the
//! no-carry optimisation, transcribed instruction for instruction. Same
//! algorithm, same intermediate values, same result: [`mont_mul`] is checked
//! against the generic implementation in the crate's tests.

/// Montgomery product of two 4-limb field elements, little-endian limbs.
///
/// Returns the result *before* the conditional subtraction of the modulus, as
/// the generic CIOS loop does; callers apply `subtract_modulus`.
///
/// # Safety
///
/// Pure register arithmetic, no memory access. Requires the no-carry
/// precondition of the algorithm: the modulus must have a spare high bit,
/// which both Pasta moduli do.
#[cfg(target_arch = "aarch64")]
#[allow(unsafe_code)] // the whole point: carry chains the compiler will not emit
#[inline(always)]
pub fn mont_mul(a: &[u64; 4], b: &[u64; 4], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    let (mut r0, mut r1, mut r2, mut r3) = (0u64, 0u64, 0u64, 0u64);
    unsafe {
        core::arch::asm!(
            // round over b0
            "mul   {t}, {a0}, {b0}",
            "umulh {u}, {a0}, {b0}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b0}",
            "umulh {u}, {a1}, {b0}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b0}",
            "umulh {u}, {a2}, {b0}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b0}",
            "umulh {u}, {a3}, {b0}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b1
            "mul   {t}, {a0}, {b1}",
            "umulh {u}, {a0}, {b1}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b1}",
            "umulh {u}, {a1}, {b1}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b1}",
            "umulh {u}, {a2}, {b1}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b1}",
            "umulh {u}, {a3}, {b1}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b2
            "mul   {t}, {a0}, {b2}",
            "umulh {u}, {a0}, {b2}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b2}",
            "umulh {u}, {a1}, {b2}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b2}",
            "umulh {u}, {a2}, {b2}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b2}",
            "umulh {u}, {a3}, {b2}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b3
            "mul   {t}, {a0}, {b3}",
            "umulh {u}, {a0}, {b3}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b3}",
            "umulh {u}, {a1}, {b3}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b3}",
            "umulh {u}, {a2}, {b3}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b3}",
            "umulh {u}, {a3}, {b3}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            a0 = in(reg) a[0],
            a1 = in(reg) a[1],
            a2 = in(reg) a[2],
            a3 = in(reg) a[3],
            b0 = in(reg) b[0],
            b1 = in(reg) b[1],
            b2 = in(reg) b[2],
            b3 = in(reg) b[3],
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            p2 = in(reg) modulus[2],
            p3 = in(reg) modulus[3],
            inv = in(reg) inv,
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            k = out(reg) _,
            c1 = out(reg) _,
            c2 = out(reg) _,
            t = out(reg) _,
            u = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    [r0, r1, r2, r3]
}

/// Same body as [`mont_mul`], operands taken by value: a reference forces the
/// limbs to memory, and the reload costs more than the multiplication saves.
#[cfg(target_arch = "aarch64")]
#[allow(unsafe_code)] // the whole point: carry chains the compiler will not emit
#[inline(always)]
pub fn mont_mul_v3(a: [u64; 4], b: [u64; 4], modulus: [u64; 4], inv: u64) -> [u64; 4] {
    let (mut r0, mut r1, mut r2, mut r3) = (0u64, 0u64, 0u64, 0u64);
    unsafe {
        core::arch::asm!(
            // round over b0
            "mul   {t}, {a0}, {b0}",
            "umulh {u}, {a0}, {b0}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b0}",
            "umulh {u}, {a1}, {b0}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b0}",
            "umulh {u}, {a2}, {b0}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b0}",
            "umulh {u}, {a3}, {b0}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b1
            "mul   {t}, {a0}, {b1}",
            "umulh {u}, {a0}, {b1}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b1}",
            "umulh {u}, {a1}, {b1}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b1}",
            "umulh {u}, {a2}, {b1}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b1}",
            "umulh {u}, {a3}, {b1}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b2
            "mul   {t}, {a0}, {b2}",
            "umulh {u}, {a0}, {b2}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b2}",
            "umulh {u}, {a1}, {b2}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b2}",
            "umulh {u}, {a2}, {b2}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b2}",
            "umulh {u}, {a3}, {b2}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b3
            "mul   {t}, {a0}, {b3}",
            "umulh {u}, {a0}, {b3}",
            "adds  {r0}, {r0}, {t}",
            "adc   {c1}, {u}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {t}, {k}, {p0}",
            "umulh {u}, {k}, {p0}",
            "adds  {t}, {r0}, {t}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a1}, {b3}",
            "umulh {u}, {a1}, {b3}",
            "adds  {r1}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p1}",
            "umulh {u}, {k}, {p1}",
            "adds  {t}, {r1}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r0}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a2}, {b3}",
            "umulh {u}, {a2}, {b3}",
            "adds  {r2}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p2}",
            "umulh {u}, {k}, {p2}",
            "adds  {t}, {r2}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r1}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "mul   {t}, {a3}, {b3}",
            "umulh {u}, {a3}, {b3}",
            "adds  {r3}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {u}, xzr",
            "mul   {t}, {k}, {p3}",
            "umulh {u}, {k}, {p3}",
            "adds  {t}, {r3}, {t}",
            "adc   {u}, {u}, xzr",
            "adds  {r2}, {t}, {c2}",
            "adc   {c2}, {u}, xzr",
            "add   {r3}, {c1}, {c2}",
            a0 = in(reg) a[0],
            a1 = in(reg) a[1],
            a2 = in(reg) a[2],
            a3 = in(reg) a[3],
            b0 = in(reg) b[0],
            b1 = in(reg) b[1],
            b2 = in(reg) b[2],
            b3 = in(reg) b[3],
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            p2 = in(reg) modulus[2],
            p3 = in(reg) modulus[3],
            inv = in(reg) inv,
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            k = out(reg) _,
            c1 = out(reg) _,
            c2 = out(reg) _,
            t = out(reg) _,
            u = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    [r0, r1, r2, r3]
}

/// Same product, with the operands loaded by the assembly itself and both
/// 64x64 products of a step issued before the carry chain that consumes them.
/// The first version passed thirteen values in registers and serialised every
/// addition; it lost to the compiler.
#[cfg(target_arch = "aarch64")]
#[allow(unsafe_code)] // the whole point: carry chains the compiler will not emit
#[inline(always)]
pub fn mont_mul_v2(a: &[u64; 4], b: &[u64; 4], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    let mut out = [0u64; 4];
    unsafe {
        core::arch::asm!(
            "ldp {a0}, {a1}, [{a_ptr}]",
            "ldp {a2}, {a3}, [{a_ptr}, #16]",
            "ldp {p0}, {p1}, [{p_ptr}]",
            "ldp {p2}, {p3}, [{p_ptr}, #16]",
            "mov {r0}, xzr",
            "mov {r1}, xzr",
            "mov {r2}, xzr",
            "mov {r3}, xzr",
            // round over b[0]
            "ldr   {bi}, [{b_ptr}, #0]",
            "mul   {m0}, {a0}, {bi}",
            "umulh {h0}, {a0}, {bi}",
            "adds  {r0}, {r0}, {m0}",
            "adc   {c1}, {h0}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {m1}, {k}, {p0}",
            "umulh {h1}, {k}, {p0}",
            "adds  {m0}, {r0}, {m1}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a1}, {bi}",
            "umulh {h0}, {a1}, {bi}",
            "mul   {m1}, {k}, {p1}",
            "umulh {h1}, {k}, {p1}",
            "adds  {r1}, {r1}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r1}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r0}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a2}, {bi}",
            "umulh {h0}, {a2}, {bi}",
            "mul   {m1}, {k}, {p2}",
            "umulh {h1}, {k}, {p2}",
            "adds  {r2}, {r2}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r2}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r1}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a3}, {bi}",
            "umulh {h0}, {a3}, {bi}",
            "mul   {m1}, {k}, {p3}",
            "umulh {h1}, {k}, {p3}",
            "adds  {r3}, {r3}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r3}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r2}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b[1]
            "ldr   {bi}, [{b_ptr}, #8]",
            "mul   {m0}, {a0}, {bi}",
            "umulh {h0}, {a0}, {bi}",
            "adds  {r0}, {r0}, {m0}",
            "adc   {c1}, {h0}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {m1}, {k}, {p0}",
            "umulh {h1}, {k}, {p0}",
            "adds  {m0}, {r0}, {m1}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a1}, {bi}",
            "umulh {h0}, {a1}, {bi}",
            "mul   {m1}, {k}, {p1}",
            "umulh {h1}, {k}, {p1}",
            "adds  {r1}, {r1}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r1}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r0}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a2}, {bi}",
            "umulh {h0}, {a2}, {bi}",
            "mul   {m1}, {k}, {p2}",
            "umulh {h1}, {k}, {p2}",
            "adds  {r2}, {r2}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r2}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r1}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a3}, {bi}",
            "umulh {h0}, {a3}, {bi}",
            "mul   {m1}, {k}, {p3}",
            "umulh {h1}, {k}, {p3}",
            "adds  {r3}, {r3}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r3}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r2}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b[2]
            "ldr   {bi}, [{b_ptr}, #16]",
            "mul   {m0}, {a0}, {bi}",
            "umulh {h0}, {a0}, {bi}",
            "adds  {r0}, {r0}, {m0}",
            "adc   {c1}, {h0}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {m1}, {k}, {p0}",
            "umulh {h1}, {k}, {p0}",
            "adds  {m0}, {r0}, {m1}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a1}, {bi}",
            "umulh {h0}, {a1}, {bi}",
            "mul   {m1}, {k}, {p1}",
            "umulh {h1}, {k}, {p1}",
            "adds  {r1}, {r1}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r1}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r0}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a2}, {bi}",
            "umulh {h0}, {a2}, {bi}",
            "mul   {m1}, {k}, {p2}",
            "umulh {h1}, {k}, {p2}",
            "adds  {r2}, {r2}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r2}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r1}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a3}, {bi}",
            "umulh {h0}, {a3}, {bi}",
            "mul   {m1}, {k}, {p3}",
            "umulh {h1}, {k}, {p3}",
            "adds  {r3}, {r3}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r3}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r2}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "add   {r3}, {c1}, {c2}",
            // round over b[3]
            "ldr   {bi}, [{b_ptr}, #24]",
            "mul   {m0}, {a0}, {bi}",
            "umulh {h0}, {a0}, {bi}",
            "adds  {r0}, {r0}, {m0}",
            "adc   {c1}, {h0}, xzr",
            "mul   {k}, {r0}, {inv}",
            "mul   {m1}, {k}, {p0}",
            "umulh {h1}, {k}, {p0}",
            "adds  {m0}, {r0}, {m1}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a1}, {bi}",
            "umulh {h0}, {a1}, {bi}",
            "mul   {m1}, {k}, {p1}",
            "umulh {h1}, {k}, {p1}",
            "adds  {r1}, {r1}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r1}, {r1}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r1}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r0}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a2}, {bi}",
            "umulh {h0}, {a2}, {bi}",
            "mul   {m1}, {k}, {p2}",
            "umulh {h1}, {k}, {p2}",
            "adds  {r2}, {r2}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r2}, {r2}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r2}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r1}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "mul   {m0}, {a3}, {bi}",
            "umulh {h0}, {a3}, {bi}",
            "mul   {m1}, {k}, {p3}",
            "umulh {h1}, {k}, {p3}",
            "adds  {r3}, {r3}, {m0}",
            "adc   {h0}, {h0}, xzr",
            "adds  {r3}, {r3}, {c1}",
            "adc   {c1}, {h0}, xzr",
            "adds  {m0}, {r3}, {m1}",
            "adc   {h1}, {h1}, xzr",
            "adds  {r2}, {m0}, {c2}",
            "adc   {c2}, {h1}, xzr",
            "add   {r3}, {c1}, {c2}",
            "stp {r0}, {r1}, [{out_ptr}]",
            "stp {r2}, {r3}, [{out_ptr}, #16]",
            a_ptr = in(reg) a.as_ptr(),
            b_ptr = in(reg) b.as_ptr(),
            p_ptr = in(reg) modulus.as_ptr(),
            out_ptr = in(reg) out.as_mut_ptr(),
            inv = in(reg) inv,
            a0 = out(reg) _, a1 = out(reg) _, a2 = out(reg) _, a3 = out(reg) _,
            p0 = out(reg) _, p1 = out(reg) _, p2 = out(reg) _, p3 = out(reg) _,
            r0 = out(reg) _, r1 = out(reg) _, r2 = out(reg) _, r3 = out(reg) _,
            m0 = out(reg) _, m1 = out(reg) _, h0 = out(reg) _, h1 = out(reg) _,
            bi = out(reg) _, k = out(reg) _, c1 = out(reg) _, c2 = out(reg) _,
            options(nostack),
        );
    }
    out
}

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use ark_ff::{
        fields::{Fp256, MontBackend, MontConfig},
        BigInt, UniformRand,
    };
    use ark_std::{eprintln, rand::SeedableRng, time::Duration, time::Instant, vec::Vec};

    use super::{mont_mul, mont_mul_v2, mont_mul_v3};
    use crate::pasta::fields::{fp::FqConfig, fq::FrConfig, Fp, Fq};

    /// The assembly must agree with the generic CIOS loop on every input, so
    /// the check is the generic implementation itself, on random elements.
    fn agrees_with_generic<C: MontConfig<4>>(rounds: usize) {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0);
        for _ in 0..rounds {
            let left = Fp256::<MontBackend<C, 4>>::rand(&mut rng);
            let right = Fp256::<MontBackend<C, 4>>::rand(&mut rng);

            let mut product = mont_mul(&left.0 .0, &right.0 .0, &C::MODULUS.0, C::INV);
            assert_eq!(
                product,
                mont_mul_v2(&left.0 .0, &right.0 .0, &C::MODULUS.0, C::INV),
                "the two assembly variants disagree"
            );
            assert_eq!(
                product,
                mont_mul_v3(left.0 .0, right.0 .0, C::MODULUS.0, C::INV),
                "the by-value variant disagrees"
            );
            // The CIOS loop leaves a result below 2p; the generic path then
            // subtracts the modulus once.
            if BigInt(product) >= C::MODULUS {
                let mut borrow = 0u64;
                for (limb, modulus) in product.iter_mut().zip(C::MODULUS.0.iter()) {
                    let (difference, first) = limb.overflowing_sub(*modulus);
                    let (difference, second) = difference.overflowing_sub(borrow);
                    *limb = difference;
                    borrow = u64::from(first || second);
                }
            }

            let expected = left * right;
            assert_eq!(
                product, expected.0 .0,
                "assembly product disagrees with the generic one"
            );
        }
    }

    #[test]
    fn matches_the_generic_multiplication_on_fp() {
        agrees_with_generic::<FqConfig>(200_000);
    }

    #[test]
    fn matches_the_generic_multiplication_on_fq() {
        agrees_with_generic::<FrConfig>(200_000);
    }

    /// Latency of a dependent multiplication chain, generic against assembly.
    #[test]
    #[ignore = "benchmark: field multiplication latency"]
    fn measure_multiplication_latency() {
        const ROUNDS: u64 = 5_000_000;
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0);

        let mut accumulator = Fp::rand(&mut rng);
        let factor = Fp::rand(&mut rng);
        let started = Instant::now();
        for _ in 0..ROUNDS {
            accumulator *= factor;
        }
        let generic = started.elapsed();
        core::hint::black_box(accumulator);

        let mut limbs = Fp::rand(&mut rng).0 .0;
        let factor = factor.0 .0;
        let started = Instant::now();
        for _ in 0..ROUNDS {
            limbs = mont_mul(&limbs, &factor, &FqConfig::MODULUS.0, FqConfig::INV);
        }
        let assembly = started.elapsed();
        core::hint::black_box(limbs);

        let mut limbs_v2 = Fp::rand(&mut rng).0 .0;
        let started = Instant::now();
        for _ in 0..ROUNDS {
            limbs_v2 = mont_mul_v2(&limbs_v2, &factor, &FqConfig::MODULUS.0, FqConfig::INV);
        }
        let assembly_v2 = started.elapsed();
        core::hint::black_box(limbs_v2);

        let mut limbs_v3 = Fp::rand(&mut rng).0 .0;
        let modulus = FqConfig::MODULUS.0;
        let started = Instant::now();
        for _ in 0..ROUNDS {
            limbs_v3 = mont_mul_v3(limbs_v3, factor, modulus, FqConfig::INV);
        }
        let assembly_v3 = started.elapsed();
        core::hint::black_box(limbs_v3);

        let nanos = |elapsed: Duration| elapsed.as_secs_f64() * 1e9 / ROUNDS as f64;
        eprintln!("generic (ark-ff portable): {:.1} ns/mul", nanos(generic));
        eprintln!("aarch64 assembly         : {:.1} ns/mul", nanos(assembly));
        eprintln!("aarch64 assembly v2      : {:.1} ns/mul", nanos(assembly_v2));
        eprintln!("aarch64 assembly v3      : {:.1} ns/mul", nanos(assembly_v3));
        eprintln!(
            "speedup                  : v1 {:.2}x, v2 {:.2}x, v3 {:.2}x",
            generic.as_secs_f64() / assembly.as_secs_f64(),
            generic.as_secs_f64() / assembly_v2.as_secs_f64(),
            generic.as_secs_f64() / assembly_v3.as_secs_f64(),
        );
        let _ = Fq::rand(&mut rng);
    }
}

#[cfg(all(test, target_arch = "aarch64"))]
mod neon_tests {
    use ark_ff::{
        fields::models::fp::{lazy29, neon29},
        UniformRand,
    };
    use ark_std::{eprintln, rand::SeedableRng, time::Duration, time::Instant, vec::Vec};

    use crate::pasta::fields::{fp::FqConfig, Fp};

    fn domain_values(count: usize) -> Vec<[u64; lazy29::LIMBS]> {
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(11);
        let entry = lazy29::entry_constant::<FqConfig>();
        (0..count)
            .map(|_| lazy29::enter::<FqConfig>(&Fp::rand(&mut rng).0, &entry))
            .collect()
    }

    /// The two lanes must agree with the scalar routine they vectorise.
    #[test]
    fn matches_the_scalar_domain_multiplication() {
        let params = lazy29::params::<FqConfig>();
        let values = domain_values(2048);
        for quad in values.chunks_exact(4) {
            let a = [quad[0], quad[1]];
            let b = [quad[2], quad[3]];
            assert_eq!(
                neon29::mont_mul2(&params, &a, &b),
                [
                    lazy29::mont_mul_p(&params, &a[0], &b[0]),
                    lazy29::mont_mul_p(&params, &a[1], &b[1]),
                ]
            );
        }
    }

    /// Throughput of the three multiplications, per single field product, with
    /// independent streams -- what the prover actually issues: the base folding
    /// and the MSM multiply thousands of unrelated elements, so latency can be
    /// hidden and NEON's wider results are not on a critical path.
    #[test]
    #[ignore = "benchmark: two-lane NEON against the scalar paths"]
    fn measure_two_lane_throughput() {
        const ROUNDS: u64 = 1_000_000;
        // Four field products per iteration in every variant, so the reported
        // figure is comparable across them.
        const PER_ROUND: f64 = 4.0;
        let params = lazy29::params::<FqConfig>();
        let values = domain_values(8);

        // NEON: two calls of two lanes, on independent data.
        let mut left = [values[0], values[1]];
        let mut right = [values[2], values[3]];
        let factor_left = [values[4], values[5]];
        let factor_right = [values[6], values[7]];
        let started = Instant::now();
        for _ in 0..ROUNDS {
            left = neon29::mont_mul2(&params, &left, &factor_left);
            right = neon29::mont_mul2(&params, &right, &factor_right);
        }
        let neon = started.elapsed();
        core::hint::black_box((&left, &right));

        // 29-bit scalar: four independent chains.
        let mut scalars = [values[0], values[1], values[2], values[3]];
        let factors = [values[4], values[5], values[6], values[7]];
        let started = Instant::now();
        for _ in 0..ROUNDS {
            for lane in 0..4 {
                scalars[lane] = lazy29::mont_mul_p(&params, &scalars[lane], &factors[lane]);
            }
        }
        let scalar29 = started.elapsed();
        core::hint::black_box(&scalars);

        // 64-bit CIOS, the production path: four independent chains too.
        let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(3);
        let mut fields = [Fp::rand(&mut rng); 4];
        for field in fields.iter_mut() {
            *field = Fp::rand(&mut rng);
        }
        let field_factors = [
            Fp::rand(&mut rng),
            Fp::rand(&mut rng),
            Fp::rand(&mut rng),
            Fp::rand(&mut rng),
        ];
        let started = Instant::now();
        for _ in 0..ROUNDS {
            for lane in 0..4 {
                fields[lane] *= field_factors[lane];
            }
        }
        let scalar64 = started.elapsed();
        core::hint::black_box(&fields);

        let per_mul =
            |elapsed: Duration| elapsed.as_secs_f64() * 1e9 / (PER_ROUND * ROUNDS as f64);
        eprintln!("64-bit CIOS (ark)     : {:.1} ns/mul", per_mul(scalar64));
        eprintln!("29-bit CIOS (scalar)  : {:.1} ns/mul", per_mul(scalar29));
        eprintln!("29-bit CIOS (NEON x2) : {:.1} ns/mul", per_mul(neon));
        eprintln!(
            "NEON vs 64-bit CIOS   : {:.2}x",
            scalar64.as_secs_f64() / neon.as_secs_f64()
        );
    }
}
