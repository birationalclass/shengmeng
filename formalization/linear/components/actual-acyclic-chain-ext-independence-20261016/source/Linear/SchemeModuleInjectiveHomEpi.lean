module
public import Linear.SchemeModuleOpenInjectives
public import Linear.SchemeModuleHomPrecompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (I : X.Modules) [Injective I]

/-- ACTUAL internal Hom into an injective sheaf sends an original mono
to a surjection on EVERY original open. Local injectivity is DERIVED
from actual extension by zero,not an added premise. -/
theorem schemeModuleHomPrecompose_app_surjective {A B : X.Modules}
    (f : A ⟶ B) [Mono f] (U : X.Opens) :
    Function.Surjective ((schemeModuleHomPrecompose (N := I) f).app U) := by
  letI := schemeModuleOverFunctor_isRightAdjoint X U
  letI := schemeModuleInjectiveOver X I U
  intro a
  refine ⟨(schemeModuleHomOverEquiv B I U)
    (Injective.factorThru ((schemeModuleHomOverEquiv A I U).symm a)
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f)),?_⟩
  change (schemeModuleHomOverEquiv A I U)
    (((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f) ≫
      (schemeModuleHomOverEquiv B I U).symm ((schemeModuleHomOverEquiv B I U)
        (Injective.factorThru ((schemeModuleHomOverEquiv A I U).symm a)
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f)))) = a
  rw [Equiv.symm_apply_apply,Injective.comp_factorThru,Equiv.apply_symm_apply]

/-- ACTUAL precomposition into an injective coefficient sheaf is epi.
This is a geometric sheaf statement,not only a module Hom computation. -/
theorem schemeModuleHomPrecompose_epi {A B : X.Modules} (f : A ⟶ B) [Mono f] :
    Epi (schemeModuleHomPrecompose (N := I) f) := by
  letI : (SheafOfModules.forget.{u} X.ringCatSheaf).ReflectsEpimorphisms :=
    Functor.reflectsEpimorphisms_of_faithful (SheafOfModules.forget.{u} X.ringCatSheaf)
  apply Functor.epi_of_epi_map (SheafOfModules.forget.{u} X.ringCatSheaf)
  apply PresheafOfModules.epi_of_surjective
  intro V
  exact schemeModuleHomPrecompose_app_surjective I f V.unop

end LinearStudy
