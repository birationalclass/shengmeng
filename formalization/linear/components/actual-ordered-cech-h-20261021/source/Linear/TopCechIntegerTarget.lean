module
public import Linear.TopCoverGeneratedTerminalSheaf
public import Mathlib.Algebra.Category.Grp.Adjunctions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- The native free abelian group on the one-point type is the SAME lifted integer object
used by native sheaf cohomology. This uses the library's unique-type equivalence. -/
def freePUnitNativeIntegerIso :
    AddCommGrpCat.free.obj PUnit.{u+1} ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
  ((FreeAbelianGroup.uniqueEquiv PUnit.{u+1}).trans AddEquiv.ulift.symm).toAddCommGrpIso

/-- The actual cover-generated,free-abelian,sheafified target maps canonically to
native constant integers,via the SAME original inclusion and native constant-functor iso. -/
def topCoverGeneratedFreeAbelianIntegerTargetMap (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
        AddCommGrpCat.free).obj (Subfunctor.ofObjects.{u} U).toFunctor) ⟶
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free).map (Subfunctor.ofObjects.{u} U).ι) ≫
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.constComp (Opens X)ᵒᵖ PUnit.{u+1} AddCommGrpCat.free).hom ≫
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    freePUnitNativeIntegerIso.hom

/-- An actual cover identifies the augmentation target with the SAME native integer SHEAF.
It is not merely a statement about a generated subpresheaf. -/
theorem topCoverGeneratedFreeAbelianIntegerTargetMap_isIso (X : TopCat.{u})
    {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ iSup U) :
    IsIso (topCoverGeneratedFreeAbelianIntegerTargetMap X U) := by
  letI := topCoverGeneratedTerminal_freeAbelian_sheafify_inclusion_isIso X U hU
  unfold topCoverGeneratedFreeAbelianIntegerTargetMap
  infer_instance
end LinearStudy
