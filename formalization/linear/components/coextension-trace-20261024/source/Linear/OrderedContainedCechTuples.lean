module
public import Linear.ModuleOrderedBaseCech
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
/-- ORIGINAL cover indices whose opens contain the SAME original test open. -/
abbrev coverIndicesContainingOpen {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (V : X.Opens) :=
  {i : ι // V ≤ U i}
/-- Actual representable generators over the original ordered intersections. -/
def orderedCechTupleSection {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) :=
  Σ a : OrderedCechIndex ι n, ULift.{u} (V ⟶ ∏ᶜ fun k : Fin (n+1) => U (a.1 k))
/-- The ACTUAL basis generators are increasing tuples of actual indices containing V.
Neither the original intersection nor its containment morphism is replaced. -/
def orderedCechTupleSectionEquiv {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) :
    orderedCechTupleSection U V n ≃ OrderedCechIndex (coverIndicesContainingOpen U V) n where
  toFun x := ⟨fun k => ⟨x.1.1 k,leOfHom (x.2.down ≫ Pi.π _ k)⟩,by
    intro i j hij
    exact x.1.2 hij⟩
  invFun a := ⟨⟨fun k => (a.1 k).val,by intro i j hij; exact a.2 hij⟩,
    ULift.up (Pi.lift fun k => homOfLE (a.1 k).property)⟩
  left_inv x := by
    rcases x with ⟨⟨a,ha⟩,f⟩
    dsimp only
    rw [Sigma.ext_iff]
    exact ⟨rfl,heq_of_eq (Subsingleton.elim _ _)⟩
  right_inv a := by
    apply Subtype.ext
    funext k
    apply Subtype.ext
    rfl
/-- The ORIGINAL ordered face sends each actual representable generator to its face. -/
def orderedCechTupleSectionDelete {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) (k : Fin (n+2)) :
    orderedCechTupleSection U V (n+1) → orderedCechTupleSection U V n :=
  fun x => ⟨x.1.delete k,ULift.up (x.2.down ≫ (orderedCechFace U n k).φ x.1)⟩
/-- This identification commutes with EVERY ORIGINAL face,including its actual containment. -/
theorem orderedCechTupleSectionEquiv_delete {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ) (k : Fin (n+2))
    (x : orderedCechTupleSection U V (n+1)) :
    orderedCechTupleSectionEquiv U V n (orderedCechTupleSectionDelete U V n k x) =
      (orderedCechTupleSectionEquiv U V (n+1) x).delete k := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  rfl
end LinearStudy
