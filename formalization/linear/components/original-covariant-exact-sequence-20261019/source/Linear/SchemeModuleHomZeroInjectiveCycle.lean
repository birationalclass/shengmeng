module
public import Linear.SchemeModuleHomToInternalExtZero
public import Linear.SchemeModuleInjectiveInternalHomNaturality
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
/-- The native degree-zero derived-functor comparison uses the SAME curried augmentation cocycle. -/
theorem schemeModuleHomZeroInjectiveCycle {P N : X.Modules}
    (I : InjectiveResolution N) (a : P ⟶ N)
    (ha : (a ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0) :
    (schemeModuleHomUnitAddEquiv P N).symm a ≫
        I.toRightDerivedZero' (schemeModuleInternalHomCoefficientFunctor X P) =
      schemeModuleInjectiveInternalHomCycleMap I P 0 ⟨a ≫ I.ι.f 0,ha⟩ := by
  apply (cancel_mono ((schemeModuleInjectiveInternalHomComplex I P).iCycles 0)).mp
  erw [Category.assoc,InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    schemeModuleInjectiveInternalHomCycleMap_i]
  exact (schemeModuleHomUnitAddEquiv_symm_postcompose P a (I.ι.f 0)).symm
end LinearStudy
