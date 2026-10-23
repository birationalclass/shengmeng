/- Copyright (c) 2026 Chris Birkbeck. Released under Apache2.0.
Formal-inclusion and face proof adapted from reviewed SchemeModuleOrderedBaseCechComparison. -/
module
public import Linear.OrderedFreePresheafValueExact
public import Linear.TopCechFreePresheafSimplicialIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicTopology
universe u v w
/-- Include SAME strictly increasing original tuples in ALL original tuples. -/
def orderedCechFormalInclusion {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) : orderedCechFormalObject U n ⟶
      (FormalCoproduct.mk _ U).power (Fin (n+1)) where
  f i := i.1
  φ _ := 𝟙 _
theorem orderedCechFace_comp_formalInclusion {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (k : Fin (n+2)) :
    orderedCechFace U n k ≫ orderedCechFormalInclusion U n =
      orderedCechFormalInclusion U (n+1) ≫ (FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun := by
  apply FormalCoproduct.hom_ext rfl
  intro i
  exact Subsingleton.elim _ _
/-- At degree zero EVERY original tuple is strictly increasing. -/
def orderedCechDegreeZeroIndexEquiv {ι : Type u} [Preorder ι] :
    OrderedCechIndex ι 0 ≃ (Fin 1 → ι) where
  toFun a := a.1
  invFun a := ⟨a,by
    intro i j h
    have hij : i = j := Fin.ext (by omega)
    subst j
    exact False.elim (lt_irrefl _ h)⟩
  left_inv a := Subtype.ext rfl
  right_inv _ := rfl
/-- The original degree-zero inclusion is an ACTUAL formal-coproduct isomorphism. -/
def orderedCechFormalDegreeZeroIso {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : orderedCechFormalObject U 0 ≅
      (FormalCoproduct.mk _ U).power (Fin 1) :=
  FormalCoproduct.isoOfComponents orderedCechDegreeZeroIndexEquiv (fun _ => Iso.refl _)
instance orderedCechFormalInclusion_zero_isIso {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : IsIso (orderedCechFormalInclusion U 0) := by
  change IsIso (orderedCechFormalDegreeZeroIso U).hom
  infer_instance
/-- The original ordered free chains map into native FULL Cech chains,including
all original faces and integer signs.This is a chain map,not yet a quasi-isomorphism. -/
def orderedToFullFormalCechChain {X : Scheme.{u}} {A : Type w} [Category.{v} A] [Preadditive A]
    (F : FormalCoproduct.{u} X.Opens ⥤ A) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (orderedFormalCechComplex F.op U).unop ⟶
      (alternatingFaceMapComplex A).obj ((FormalCoproduct.mk _ U).cech ⋙ F) := by
  refine ChainComplex.ofHom (fun n => F.map (orderedCechFormalInclusion U n)) ?_
  intro n
  simp only [HomologicalComplex.unop_d,orderedFormalCechComplex_d,
    orderedFormalCechDifferential,orderedFormalCechCoface,Functor.op_map,
    unop_sum,unop_zsmul,Quiver.Hom.unop_op,
    alternatingFaceMapComplex_obj_d,AlternatingFaceMapComplex.objD,Functor.comp_map,
    comp_sum,sum_comp,comp_zsmul,zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change F.map (orderedCechFormalInclusion U (n+1)) ≫
    F.map ((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun) =
      F.map (orderedCechFace U n k) ≫ F.map (orderedCechFormalInclusion U n)
  rw [← F.map_comp,← F.map_comp,orderedCechFace_comp_formalInclusion U n k]
end LinearStudy
