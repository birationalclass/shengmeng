module
public import Linear.SchemeModuleHomAffineTransportSections
public import Linear.NativeAffineInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) {P Q : (Spec R).Modules}
/-- The source action is induced by the actual specified chart ring homomorphism. -/
@[instance_reducible] def schemeModuleHomChartBaseModule (φ : R →+* Γ(X,U)) :
    Module R Γ(schemeModuleHomModuleSheaf M N,U) :=
  Module.compHom _ φ
/-- Actual Hom section linear equivalence; the scalar square is explicit and later derived for the original chart. -/
def schemeModuleHomAffineTransportSectionsLinearEquiv
    (φ : R →+* Γ(X,U))
    (hφ : ∀ r : R, e.inv.appTop (U.topIso.inv (φ r)) = (Scheme.ΓSpecIso R).inv r)
    (α : M.restrict (e.inv ≫ U.ι) ≅ P)
    (β : N.restrict (e.inv ≫ U.ι) ≅ Q) :
    letI := schemeModuleHomChartBaseModule M N U R φ
    letI := originalAffineHomBaseModule R P Q
    Γ(schemeModuleHomModuleSheaf M N,U) ≃ₗ[R] Γ(schemeModuleHomModuleSheaf P Q,⊤) := by
  letI := schemeModuleHomChartBaseModule M N U R φ
  letI := originalAffineHomBaseModule R P Q
  exact {
    __ := schemeModuleHomAffineTransportSectionsEquiv M N U R e α β
    map_add' := schemeModuleHomAffineTransportSectionsEquiv_add M N U R e α β
    map_smul' := by
      intro r h
      have hs := schemeModuleHomAffineTransportSectionsEquiv_smul M N U R e α β (φ r) h
      rw [hφ] at hs
      exact hs }
end LinearStudy
