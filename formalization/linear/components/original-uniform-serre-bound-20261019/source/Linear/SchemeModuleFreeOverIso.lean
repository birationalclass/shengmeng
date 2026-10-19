module
public import Linear.SchemeModuleUnitHomSections
public import Linear.SchemeModuleInternalHomSourceLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual finite free sheaf RESTRICTED to U is the native finite free
sheaf over SAME Over(U). Reuse native mapFreeIso and PROVED preservation
of finite colimits,retaining actual structure-sheaf unit restriction. -/
def schemeModuleFreeOverIso (U : X.Opens) (ι : Type u) [Finite ι] :
    (SheafOfModules.free (R := X.ringCatSheaf) ι).over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) ι := by
  letI := schemeModuleOverFunctor_preservesFiniteColimits X U
  exact (SheafOfModules.mapFreeIso
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) ι
      (schemeModuleUnitOverIso X U).symm).symm

end LinearStudy
