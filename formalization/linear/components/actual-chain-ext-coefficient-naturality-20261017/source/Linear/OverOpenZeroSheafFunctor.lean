module
public import Linear.OverOpenZeroPresheafFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Preorder C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- ACTUAL sheaf extension by zero:forget the local sheaf,extend by
actual presheaf direct sums,and apply native exact sheafification. -/
def overOpenZeroSheafFunctor : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R :=
  SheafOfModules.forget (R.over U) ⋙ overOpenZeroPresheafFunctor R.obj U ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

/-- Mono preservation is PROVED from actual presheaf direct sums and
native finite-limit preservation of sheafification,not an extra premise. -/
theorem overOpenZeroSheafFunctor_preservesMonomorphisms :
    (overOpenZeroSheafFunctor R U).PreservesMonomorphisms := by
  letI := overOpenZeroPresheafFunctor_preservesMonomorphisms R.obj U
  unfold overOpenZeroSheafFunctor
  infer_instance

end LinearStudy
