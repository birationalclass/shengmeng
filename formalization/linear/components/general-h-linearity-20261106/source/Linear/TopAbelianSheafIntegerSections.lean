module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Actual global sections corepresent morphisms from the native constant integer SHEAF. -/
def topAbelianSheafIntegerHomSectionsAddEquiv (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ F) ≃+ F.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The SAME integer-source section equivalence is coefficient-natural. -/
theorem topAbelianSheafIntegerHomSectionsAddEquiv_postcompose (X : TopCat.{u})
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    topAbelianSheafIntegerHomSectionsAddEquiv X G (a ≫ f) =
      f.hom.app (op ⊤) (topAbelianSheafIntegerHomSectionsAddEquiv X F a) := by
  simp only [topAbelianSheafIntegerHomSectionsAddEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl
end LinearStudy
