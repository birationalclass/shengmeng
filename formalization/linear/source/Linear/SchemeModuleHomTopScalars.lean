module
public import Linear.OriginalGlobalModuleScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The SAME global section equivalence carries scalar multiplication
to postcomposition with the actual structure-sheaf scalar endomorphism. -/
theorem schemeModuleHomTopSectionsEquiv_smul (r : Γ(X,⊤))
    (h : Γ(schemeModuleHomModuleSheaf M N,⊤)) :
    schemeModuleHomTopSectionsEquiv M N (r • h) =
      schemeModuleHomTopSectionsEquiv M N h ≫ originalGlobalModuleScalar r N := by
  apply SheafOfModules.hom_ext
  ext U x
  rfl

/-- Addition is preserved by the SAME actual global-section comparison. -/
theorem schemeModuleHomTopSectionsEquiv_add
    (h k : Γ(schemeModuleHomModuleSheaf M N,⊤)) :
    schemeModuleHomTopSectionsEquiv M N (h + k) =
      schemeModuleHomTopSectionsEquiv M N h + schemeModuleHomTopSectionsEquiv M N k := by
  apply SheafOfModules.hom_ext
  ext U x
  rfl

end LinearStudy
