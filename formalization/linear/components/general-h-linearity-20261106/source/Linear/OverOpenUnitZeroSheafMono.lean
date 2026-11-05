module
public import Linear.OverOpenUnitZeroPresheafMono
public import Linear.OverOpenZeroSheafAdjunction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Preorder C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The actual local-unit inclusion via native exact sheafification and its counit. -/
def overOpenUnitZeroSheafToUnit :
    (overOpenZeroSheafFunctor R U).obj (SheafOfModules.unit (R.over U)) ⟶
      SheafOfModules.unit R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
      (overOpenUnitZeroPresheafToUnit R.obj U) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app
      (SheafOfModules.unit R)

/-- Exact sheafification preserves the proved original presheaf monomorphism. -/
theorem overOpenUnitZeroSheafToUnit_mono : Mono (overOpenUnitZeroSheafToUnit R U) := by
  letI := overOpenUnitZeroPresheafToUnit_mono R.obj U
  unfold overOpenUnitZeroSheafToUnit
  infer_instance
end LinearStudy
