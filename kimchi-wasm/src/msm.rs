use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use paste::paste;
use wasm_bindgen::prelude::*;

use crate::wasm_vector::WasmVector;
use wasm_types::FlatVector as WasmFlatVector;

macro_rules! impl_msm {
    ($name:ident, $WasmG:ty, $WasmF:ty, $G:ty) => {
        paste! {
            #[wasm_bindgen]
            pub fn [<caml_ $name:snake _msm>](
                points: WasmVector<$WasmG>,
                scalars: WasmFlatVector<$WasmF>,
            ) -> Result<$WasmG, JsValue> {
                let points: Vec<$G> = points.into_iter().map(Into::into).collect();
                let scalars: Vec<<$G as AffineRepr>::ScalarField> =
                    scalars.into_iter().map(Into::into).collect();

                if points.len() != scalars.len() {
                    return Err(JsValue::from_str(&format!(
                        "caml_{}_msm: points/scalars length mismatch ({} != {})",
                        stringify!($name),
                        points.len(),
                        scalars.len()
                    )));
                }

                let scalars_bigint: Vec<_> =
                    scalars.into_iter().map(PrimeField::into_bigint).collect();
                let result = <$G as AffineRepr>::Group::msm_bigint(&points, &scalars_bigint);
                Ok(result.into_affine().into())
            }
        }
    };
}

pub mod pallas {
    use super::*;
    use arkworks::{WasmGPallas, WasmPastaFq};
    use mina_curves::pasta::Pallas as GAffine;

    impl_msm!(pallas, WasmGPallas, WasmPastaFq, GAffine);
}

pub mod vesta {
    use super::*;
    use arkworks::{WasmGVesta, WasmPastaFp};
    use mina_curves::pasta::Vesta as GAffine;

    impl_msm!(vesta, WasmGVesta, WasmPastaFp, GAffine);
}
