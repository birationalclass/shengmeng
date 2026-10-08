module
public import Linear.FieldEndomorphismSimpleImage
public import Linear.TranscendentalAdjoinBaseDegree
public import Linear.StableFieldImageDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy

/-- The degree of the WHOLE original ambient image factors into its
one-variable degree and the actual restricted coefficient-map degree. -/
theorem fieldEndomorphism_rational_degree_factor
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (E : IntermediateField k F) (φ : F →ₐ[k] F) (σ : E →ₐ[k] E)
    (hc : ∀ a : E, φ (a : F) = (σ a : F))
    [Module.Finite σ.fieldRange E] (t : F)
    (hgen : IntermediateField.adjoin E {t} = ⊤)
    (ht : Transcendental E (φ t)) :
    Module.finrank φ.fieldRange F =
      Module.finrank (IntermediateField.adjoin E {φ t}) F *
        Module.finrank σ.fieldRange E := by
  let R := E.map φ
  let ν := IntermediateField.inclusion (stableField_image_le E φ σ hc)
  letI : Algebra R E := ν.toRingHom.toAlgebra
  letI : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hR := stableField_image_finrank_and_finite E φ σ hc
  letI : Module.Finite R E := hR.2
  letI : Algebra.IsAlgebraic R E := inferInstance
  let L := IntermediateField.adjoin R {φ t}
  let M := IntermediateField.adjoin E {φ t}
  letI : Algebra L M := (transcendentalAdjoinScalarInclusion R E F (φ t)).toRingHom.toAlgebra
  letI : IsScalarTower L M F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcoef : Module.finrank L M = Module.finrank σ.fieldRange E :=
    (transcendental_adjoin_base_finrank R E F (φ t) ht).trans hR.1
  have hImage : φ.fieldRange = L.restrictScalars k :=
    fieldEndomorphism_simple_fieldRange E t φ hgen
  have hwhole : Module.finrank φ.fieldRange F = Module.finrank L F := by
    rw [hImage]
    rfl
  rw [hwhole]
  calc
    Module.finrank L F = Module.finrank L M * Module.finrank M F :=
      (Module.finrank_mul_finrank L M F).symm
    _ = Module.finrank M F * Module.finrank σ.fieldRange E := by
      rw [hcoef, Nat.mul_comm]

end LinearStudy
