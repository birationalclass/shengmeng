module
public import Linear.SchemeModuleUnitHomIso
public import Linear.SchemeModuleDerivedInternalHom
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL internal Hom from the SAME unit preserves finite limits. -/
theorem schemeModuleUnitHomCoefficient_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits
      (schemeModuleInternalHomCoefficientFunctor X (SheafOfModules.unit X.ringCatSheaf)) :=
  preservesFiniteLimits_of_natIso (schemeModuleInternalHomUnitCoefficientIso X).symm

/-- ACTUAL internal Hom from the SAME unit is right exact as well. -/
theorem schemeModuleUnitHomCoefficient_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits
      (schemeModuleInternalHomCoefficientFunctor X (SheafOfModules.unit X.ringCatSheaf)) :=
  preservesFiniteColimits_of_natIso (schemeModuleInternalHomUnitCoefficientIso X).symm

/-- Actual derived SHEAF Ext from O_X is computed by the SAME native
coefficient resolution itself,using the PROVED actual internal-Hom iso. -/
def schemeModuleUnitInternalExtResolutionIso (N : X.Modules) (q : ℕ)
    (I : InjectiveResolution N) :
    schemeModuleInternalExt (SheafOfModules.unit X.ringCatSheaf) N q ≅
      I.cocomplex.homology q :=
  schemeModuleInternalExtInjectiveResolutionIso (SheafOfModules.unit X.ringCatSheaf) N q I ≪≫
    (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) q).mapIso
      ((NatIso.mapHomologicalComplex (schemeModuleInternalHomUnitCoefficientIso X)
        (ComplexShape.up ℕ)).app I.cocomplex ≪≫
          (Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℕ)).app I.cocomplex)

/-- Positive ACTUAL derived SHEAF Ext from O_X vanishes for EVERY
actual coefficient. This does NOT assert GLOBAL Ext(O_X,N)=0. -/
theorem schemeModuleUnitInternalExt_succ (N : X.Modules) (q : ℕ) :
    IsZero (schemeModuleInternalExt (SheafOfModules.unit X.ringCatSheaf) N (q+1)) :=
  IsZero.of_iso ((injectiveResolution N).cocomplex_exactAt_succ q).isZero_homology
    (schemeModuleUnitInternalExtResolutionIso N (q+1) (injectiveResolution N))

end LinearStudy
