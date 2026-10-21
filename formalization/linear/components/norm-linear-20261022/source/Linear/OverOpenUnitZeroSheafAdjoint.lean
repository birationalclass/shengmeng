module
public import Linear.OverOpenUnitZeroSheafMono
public import Linear.OverOpenUnitZeroSheafBinding
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

/-- Forward comparison through the actual two adjunctions. -/
theorem overOpenZeroSheafHomEquiv_val (N : SheafOfModules.{u} (R.over U))
    (M : SheafOfModules.{u} R) (a : (overOpenZeroSheafFunctor R U).obj N ⟶ M) :
    (overOpenZeroSheafHomEquiv R U N M a).val =
      overOpenZeroHomRestrict R.obj U N.val M.val
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ a) := rfl

/-- The layerification adjunction recovers the same original unit-presheaf map. -/
theorem overOpenUnitZeroSheafToUnit_presheafAdjoint :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
      (overOpenUnitZeroSheafToUnit R U) = overOpenUnitZeroPresheafToUnit R.obj U := by
  exact overOpenUnitZeroBoundPresheafToUnit_homEquiv R U

/-- The mono corresponds exactly to the identity of the original restricted unit. -/
theorem overOpenUnitZeroSheafToUnit_adjoint :
    overOpenZeroSheafHomEquiv R U _ _ (overOpenUnitZeroSheafToUnit R U) = 𝟙 _ := by
  apply (SheafOfModules.forget (R.over U)).map_injective
  change (overOpenZeroSheafHomEquiv R U _ _ (overOpenUnitZeroSheafToUnit R U)).val = 𝟙 _
  exact (overOpenZeroSheafHomEquiv_val R U _ _ (overOpenUnitZeroSheafToUnit R U)).trans
    ((congrArg (overOpenZeroHomRestrict R.obj U _ _)
      (overOpenUnitZeroSheafToUnit_presheafAdjoint R U)).trans
        ((overOpenZeroHomEquiv R.obj U _ _).apply_symm_apply (𝟙 _)))
end LinearStudy
