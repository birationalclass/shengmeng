module
public import Linear.SchemeModuleHomZeroInjectiveCycle
public import Linear.SchemeModuleInjectiveCocycleEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- The actual degree-zero comparison is the SAME actual augmentation cocycle under ANY coefficient resolution. -/
theorem schemeModuleHomToInternalExtZero_viaResolution {P N : X.Modules}
    (I : InjectiveResolution N) (a : P ⟶ N)
    (ha : (a ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0) :
    schemeModuleHomToInternalExtZero P N a =
      schemeModuleInjectiveCocycleToInternalExt I P 0 ⟨a ≫ I.ι.f 0,ha⟩ := by
  change (schemeModuleHomUnitAddEquiv P N).symm a ≫
    ((schemeModuleInternalExtZeroIso P).app N).inv = _
  rw [schemeModuleInternalExtZeroIso_inv_app,I.toRightDerivedZero_eq]
  erw [← Category.assoc,← Category.assoc,schemeModuleHomZeroInjectiveCycle I a ha]
  rfl
end LinearStudy
