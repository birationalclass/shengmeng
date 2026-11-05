module
public import Linear.OriginalGlobalModuleScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}

/-- Every ACTUAL O-linear morphism commutes with multiplication by the
same actual global structure section, on every original open. -/
theorem originalGlobalModuleScalar_naturality (r : Γ(X,⊤))
    {M N : X.Modules} (f : M ⟶ N) :
    originalGlobalModuleScalar r M ≫ f = f ≫ originalGlobalModuleScalar r N := by
  apply SheafOfModules.hom_ext
  ext U x
  change f.app U.unop (X.presheaf.map U.unop.leTop.op r • x) =
    X.presheaf.map U.unop.leTop.op r • (show Γ(N,U.unop) from f.app U.unop x)
  exact (f.val.app U).hom.map_smul _ _

end LinearStudy
