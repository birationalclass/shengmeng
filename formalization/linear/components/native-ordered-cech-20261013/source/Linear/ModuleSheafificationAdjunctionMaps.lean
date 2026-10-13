module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe v v' u u'
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The universal map from actual module-sheafification is exactly
the sheafified presheaf map followed by the actual counit. -/
theorem moduleSheafificationHomEquiv_symm_eq
    {P : PresheafOfModules.{v} R.obj} {F : SheafOfModules.{v} R}
    (f : P ⟶ F.val) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map f ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app F := by
  have he : (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P F =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) :=
    Equiv.ext (fun g => PresheafOfModules.sheafificationAdjunction_homEquiv_apply
      (𝟙 R.obj) g)
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_counit P F f
  rw [he] at h
  exact h

/-- When actual sheafification makes the given presheaf map an
isomorphism, its actual universal map to the target sheaf is an isomorphism. -/
theorem moduleSheafificationHomEquiv_symm_isIso
    {P : PresheafOfModules.{v} R.obj} {F : SheafOfModules.{v} R}
    (f : P ⟶ F.val)
    [IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f) := by
  rw [moduleSheafificationHomEquiv_symm_eq R f]
  infer_instance

end LinearStudy
