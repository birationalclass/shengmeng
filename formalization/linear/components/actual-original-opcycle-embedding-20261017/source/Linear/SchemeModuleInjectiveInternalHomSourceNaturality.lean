module
public import Linear.SchemeModuleHomUnitSourceNaturality
public import Linear.InjectiveCocycleSourceNaturality
public import Linear.SchemeModuleInjectiveInternalHomNaturality
public import Linear.SchemeModuleInternalExtSourceMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {N : X.Modules} (I : InjectiveResolution N)

/-- Source precomposition preserves the SAME actual curried cycle. -/
theorem schemeModuleInjectiveInternalHomCycleMap_sourceNaturality
    {P Q : X.Modules} (g : P ⟶ Q) (q : ℕ) (f : injectiveCocycleGroup I Q q) :
    schemeModuleInjectiveInternalHomCycleMap I P q (injectiveCocyclePrecompose I g q f) =
      schemeModuleInjectiveInternalHomCycleMap I Q q f ≫
        HomologicalComplex.cyclesMap (schemeModuleHomCoefficientComplexMap g I.cocomplex) q := by
  apply (cancel_mono ((schemeModuleInjectiveInternalHomComplex I P).iCycles q)).mp
  erw [schemeModuleInjectiveInternalHomCycleMap_i,Category.assoc,
    HomologicalComplex.cyclesMap_i,← Category.assoc,schemeModuleInjectiveInternalHomCycleMap_i]
  exact schemeModuleHomUnitAddEquiv_symm_precompose g f.val

/-- The SAME actual sheaf cohomology class is source-natural. -/
theorem schemeModuleInjectiveInternalHomClassMap_sourceNaturality
    {P Q : X.Modules} (g : P ⟶ Q) (q : ℕ) (f : injectiveCocycleGroup I Q q) :
    schemeModuleInjectiveInternalHomClassMap I P q (injectiveCocyclePrecompose I g q f) =
      schemeModuleInjectiveInternalHomClassMap I Q q f ≫
        HomologicalComplex.homologyMap (schemeModuleHomCoefficientComplexMap g I.cocomplex) q := by
  change (_ ≫ (schemeModuleInjectiveInternalHomComplex I P).homologyπ q) =
    (_ ≫ (schemeModuleInjectiveInternalHomComplex I Q).homologyπ q) ≫ _
  erw [schemeModuleInjectiveInternalHomCycleMap_sourceNaturality,Category.assoc,
    ← HomologicalComplex.homologyπ_naturality,← Category.assoc]

end LinearStudy
