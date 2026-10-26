module
public import Linear.OverOpenZeroSheafAdjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
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

/-- ACTUAL restriction has the CONSTRUCTED sheaf extension left adjoint. -/
theorem overOpenRestriction_isRightAdjoint :
    (SheafOfModules.overFunctor.{u} R U).IsRightAdjoint :=
  (overOpenZeroSheafAdjunction R U).isRightAdjoint

/-- Stacks03F3(1) for the actual principal-open site:restriction
preserves injective module sheaves. The adjunction and mono preservation
have been PROVED for actual functors,not supplied as premises. -/
theorem overOpenRestriction_preservesInjectiveObjects :
    (SheafOfModules.overFunctor.{u} R U).PreservesInjectiveObjects := by
  letI := overOpenZeroSheafFunctor_preservesMonomorphisms R U
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (overOpenZeroSheafAdjunction R U)

end LinearStudy
