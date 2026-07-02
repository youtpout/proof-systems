//! Tests for `#[derive(SnarkyType)]` (provided by the `snarky-deriver` crate).

use ark_ff::PrimeField;
use mina_curves::pasta::Fp;
use snarky::prelude::*;
use snarky_deriver::SnarkyType;

#[derive(Debug, SnarkyType)]
struct Point<F>
where
    F: PrimeField,
{
    x: FieldVar<F>,
    y: FieldVar<F>,
}

#[test]
fn derived_size_in_field_elements() {
    assert_eq!(<Point<Fp> as SnarkyType<Fp>>::SIZE_IN_FIELD_ELEMENTS, 2);
}

#[test]
fn derived_value_roundtrip() {
    let value = (Fp::from(3u64), Fp::from(4u64));
    let (fields, aux) = <Point<Fp> as SnarkyType<Fp>>::value_to_field_elements(&value);
    assert_eq!(fields, vec![Fp::from(3u64), Fp::from(4u64)]);
    let back = <Point<Fp> as SnarkyType<Fp>>::value_of_field_elements(fields, aux);
    assert_eq!(back, value);
}

#[test]
fn derived_cvars_roundtrip() {
    let point = Point::<Fp> {
        x: FieldVar::Constant(Fp::from(1u64)),
        y: FieldVar::Constant(Fp::from(2u64)),
    };
    let (cvars, aux) = point.to_cvars();
    assert_eq!(cvars.len(), 2);
    let point2 = Point::<Fp>::from_cvars_unsafe(cvars, aux);
    let (cvars2, _) = point2.to_cvars();
    assert_eq!(cvars2.len(), 2);
}
