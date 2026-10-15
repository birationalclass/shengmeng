module
public import Linear.SchemeModuleInternalHomCoefficientFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.Algebra.Category.Grp.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

/-- On each ORIGINAL open,ACTUAL internal-Hom sections are the native
representable Hom after actual Over restriction,including coefficient maps. -/
def schemeModuleInternalHomCoefficientSectionIso (X : Scheme.{u}) (P : X.Modules)
    (U : X.Opens) :
    schemeModuleInternalHomCoefficientFunctor X P ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
          forget (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) ≅
      SheafOfModules.overFunctor.{u} X.ringCatSheaf U ⋙ coyoneda.obj (op (P.over U)) :=
  NatIso.ofComponents (fun N => (schemeModuleHomModuleSectionsEquiv P N U).toIso) (by
    intro M N c
    apply ConcreteCategory.hom_ext
    intro f
    change (schemeModuleHomOverEquiv P N U).symm
      ((schemeModuleHomOverEquiv P N U) _) = _
    exact Equiv.symm_apply_apply _ _)

/-- Actual Over restriction preserves finite limits,as seen on ORIGINAL
underlying presheaves. No projectivity or affine vanishing is a premise. -/
theorem schemeModuleOverFunctor_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) := by
  let R := X.ringCatSheaf
  let F : X.Modules ⥤ SheafOfModules.{u} (R.over U) := SheafOfModules.overFunctor R U
  let G : SheafOfModules.{u} (R.over U) ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget (R.over U) ⋙
    PresheafOfModules.toPresheaf (R.over U).obj
  letI : G.ReflectsIsomorphisms := reflectsIsomorphisms_comp _ _
  letI : ReflectsFiniteLimits G := reflectsFiniteLimits_of_reflectsIsomorphisms G
  let e : F ⋙ G ≅ (Scheme.Modules.toPresheaf X) ⋙
      (Functor.whiskeringLeft (Over U)ᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Over.forget U).op :=
    Iso.refl _
  letI : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
  letI : PreservesFiniteLimits ((Functor.whiskeringLeft (Over U)ᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Over.forget U).op) := inferInstance
  letI : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- ACTUAL internal Hom in its coefficient variable is left exact.
Prove this by original sections and native representable Hom,then reflect
limits through the faithful underlying presheaf;no desired exactness input. -/
theorem schemeModuleInternalHomCoefficientFunctor_preservesFiniteLimits
    (X : Scheme.{u}) (P : X.Modules) :
    PreservesFiniteLimits (schemeModuleInternalHomCoefficientFunctor X P) := by
  let F := schemeModuleInternalHomCoefficientFunctor X P
  let G := Scheme.Modules.toPresheaf X
  letI : ReflectsFiniteLimits G := reflectsFiniteLimits_of_reflectsIsomorphisms G
  letI : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_evaluation _ (fun U => by
      let E := (F ⋙ G) ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj U
      letI := schemeModuleOverFunctor_preservesFiniteLimits X U.unop
      letI : PreservesFiniteLimits (E ⋙ forget AddCommGrpCat.{u}) :=
        preservesFiniteLimits_of_natIso
          (schemeModuleInternalHomCoefficientSectionIso X P U.unop).symm
      exact preservesFiniteLimits_of_reflects_of_preserves E (forget AddCommGrpCat.{u}))
  exact preservesFiniteLimits_of_reflects_of_preserves F G

end LinearStudy
