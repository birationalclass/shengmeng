module
public import Linear.SchemeModuleInternalHomBifunctor
public import Linear.SchemeModuleInternalHomCoefficientLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Lattice
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

/-- On EVERY original open,the SAME contravariant internal Hom is the
native representable Hom after ACTUAL original source restriction. -/
def schemeModuleInternalHomSourceSectionIso (X : Scheme.{u}) (N : X.Modules) (U : X.Opens) :
    schemeModuleInternalHomFunctor X N ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
          forget (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) ≅
      (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).op ⋙ yoneda.obj (N.over U) :=
  NatIso.ofComponents (fun P => (schemeModuleHomModuleSectionsEquiv P.unop N U).toIso) (by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro a
    change (schemeModuleHomOverEquiv B.unop N U).symm
      ((schemeModuleHomOverEquiv B.unop N U) _) = _
    exact Equiv.symm_apply_apply _ _)

/-- ACTUAL open restriction preserves finite colimits by the EXISTING
native restriction/direct-image adjunction. No affine vanishing is assumed. -/
theorem schemeModuleOverFunctor_preservesFiniteColimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) := by
  letI : (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  infer_instance

/-- ACTUAL internal Hom in the source-opposite variable is left exact.
Reflect finite limits through ORIGINAL sheaf sections and native Yoneda. -/
theorem schemeModuleInternalHomFunctor_preservesFiniteLimits (X : Scheme.{u}) (N : X.Modules) :
    PreservesFiniteLimits (schemeModuleInternalHomFunctor X N) := by
  let F := schemeModuleInternalHomFunctor X N
  let G := Scheme.Modules.toPresheaf X
  letI : ReflectsFiniteLimits G := reflectsFiniteLimits_of_reflectsIsomorphisms G
  letI : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_evaluation _ (fun U => by
      let E := (F ⋙ G) ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj U
      letI := schemeModuleOverFunctor_preservesFiniteColimits X U.unop
      letI : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U.unop).op :=
        preservesFiniteLimits_op _
      letI : PreservesFiniteLimits (E ⋙ forget AddCommGrpCat.{u}) :=
        preservesFiniteLimits_of_natIso (schemeModuleInternalHomSourceSectionIso X N U.unop).symm
      exact preservesFiniteLimits_of_reflects_of_preserves E (forget AddCommGrpCat.{u}))
  exact preservesFiniteLimits_of_reflects_of_preserves F G

end LinearStudy
