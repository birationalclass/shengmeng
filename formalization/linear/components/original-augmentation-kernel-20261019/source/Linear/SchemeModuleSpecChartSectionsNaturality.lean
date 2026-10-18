module
public import Linear.SchemeModuleSpecChartSectionsLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- Actual original Spec-chart section transport commutes with EVERY actual
original sheaf-module morphism. No naturality certificate is supplied. -/
theorem schemeModuleSpecChartSectionsLinearEquiv_naturality
    {M N : X.Modules} (f : Spec R ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hi : f ''ᵁ ⊤ = U) (φ : R ⟶ Γ(X,U))
    (hφ : φ ≫ f.appLE U ⊤ (by rw [← hi]; exact (f.preimage_image_eq ⊤).ge) =
      (Scheme.ΓSpecIso R).inv) (α : M ⟶ N) (x : Γ(M,U)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor f).map α)).hom
      (schemeModuleSpecChartSectionsLinearEquiv M f U hi φ hφ x) =
    schemeModuleSpecChartSectionsLinearEquiv N f U hi φ hφ (α.app U x) := by
  change α.app (f ''ᵁ ⊤) (M.presheaf.map (eqToHom hi).op x) =
    N.presheaf.map (eqToHom hi).op (α.app U x)
  exact congrArg (fun g => g x) (α.mapPresheaf.naturality (eqToHom hi).op)

end LinearStudy
