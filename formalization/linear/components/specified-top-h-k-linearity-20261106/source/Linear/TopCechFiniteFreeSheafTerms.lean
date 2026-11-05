module
public import Linear.TopCechFreePresheafSimplicialIso
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace Opposite
universe u
/-- Each actual free-SHEAF Cech chain term of a finite original cover is the actual
finite coproduct of the SAME free-open sheaves on the original intersections.
Only the component isomorphism is needed;no full sheaf-coproduct instance search. -/
def topCechFiniteFreeSheafTermIso (X : TopCat.{u}) {ι : Type u} [Finite ι]
    (U : ι → Opens X) (n : ℕ) :
    ((alternatingFaceMapComplex _).obj (topCechFreeAbelianAugmented X U).left).X n ≅
      ∐ (fun i : Fin (n+1) → ι => (topOpenFreeAbelianSheafFunctor X).obj
        (∏ᶜ fun k : Fin (n+1) => U (i k))) := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  letI : HasColimitsOfShape (Discrete (Fin (n+1) → ι)) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape
  letI : HasColimitsOfShape (Discrete (Fin (n+1) → ι))
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let K := topOpenFreeAbelianPresheafFunctor X
  change S.obj ((topCechFreeAbelianPresheafAugmented X U).left.obj (op (SimplexCategory.mk n))) ≅ _
  refine S.mapIso ((topCechFreePresheafSimplicialIso X U).app (op (SimplexCategory.mk n))) ≪≫ ?_
  change S.obj (∐ (fun i : Fin (n+1) → ι => K.obj (∏ᶜ fun k : Fin (n+1) => U (i k)))) ≅ _
  letI : HasCoproduct (fun i : Fin (n+1) → ι => S.obj (K.obj (∏ᶜ fun k : Fin (n+1) => U (i k)))) := by
    change HasCoproduct (fun i : Fin (n+1) → ι =>
      (topOpenFreeAbelianSheafFunctor X).obj (∏ᶜ fun k : Fin (n+1) => U (i k)))
    infer_instance
  exact PreservesCoproduct.iso S (fun i : Fin (n+1) → ι => K.obj (∏ᶜ fun k : Fin (n+1) => U (i k)))
end LinearStudy
