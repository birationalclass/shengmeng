module
public import Linear.SchemeModuleSpecChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- Linear transport of the SAME actual sections into the original Spec
chart. Scalar compatibility is the actual chart ring pullback equation. -/
def schemeModuleSpecChartSectionsLinearEquiv
    (M : X.Modules) (f : Spec R ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (himage : f ''ᵁ ⊤ = U) (φ : R ⟶ Γ(X,U))
    (hφ : φ ≫ f.appLE U ⊤ (by rw [← himage]; exact (f.preimage_image_eq ⊤).ge) =
      (Scheme.ΓSpecIso R).inv) :
    letI : Module R Γ(M,U) := Module.compHom Γ(M,U) φ.hom
    Γ(M,U) ≃ₗ[R] moduleSpecΓFunctor.obj (M.restrict f) := by
  letI : Module R Γ(M,U) := Module.compHom Γ(M,U) φ.hom
  let E := schemeModuleSpecChartSectionsEquiv M f U himage
  exact {
    toAddEquiv := E
    map_smul' := fun c x => by
      change E (φ c • x) = (Scheme.ΓSpecIso R).inv c • E x
      exact schemeModuleSpecChartSectionsEquiv_smul M f U himage φ hφ c x }
end LinearStudy
