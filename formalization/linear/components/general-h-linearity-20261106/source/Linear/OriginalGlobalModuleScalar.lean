module
public import Linear.SchemeModuleHomTopSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}

/-- Multiplication by an actual global ORIGINAL structure-sheaf section
as an actual endomorphism of the original O-module sheaf. -/
def originalGlobalModuleScalar (r : Γ(X,⊤)) (M : X.Modules) : M ⟶ M :=
  schemeModuleHomTopSectionsEquiv M M
    (r • (schemeModuleHomTopSectionsEquiv M M).symm (𝟙 M))

/-- The constructed endomorphism is exactly multiplication by the actual
restriction of r on EVERY original open, not merely at global sections. -/
theorem originalGlobalModuleScalar_app (r : Γ(X,⊤)) (M : X.Modules)
    (U : X.Opens) (x : Γ(M,U)) :
    (originalGlobalModuleScalar r M).app U x =
      X.presheaf.map U.leTop.op r • x := rfl

end LinearStudy
