module
public import Linear.AdjunctionCounitHomEquiv
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Category C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- Native module-sheafification identity before specializing any original open or unit. -/
theorem moduleSheafification_homEquiv_map_counit
    (P : PresheafOfModules.{u} R.obj) (M : SheafOfModules.{u} R)
    (g : P ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P M
      ((PresheafOfModules.sheafification (𝟙 R.obj)).map g ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M) = g :=
  adjunction_homEquiv_map_counit
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) P M g
end LinearStudy
