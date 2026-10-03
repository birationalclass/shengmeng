module

public import Negativity.ProjPolynomialSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Final theorem: an actual finite map to a finite projective product
constructs actual Cartier equations and effective coordinate sections
with an affine nonvanishing cover. The sole product-chart property is
geometric affineness, supplied by the constructed relative product;
no divisor, section, support identity or positive degree is an input. -/
theorem exists_actual_projective_product_cartier_sections
    (R : Type u) [CommRing R] (n : ℕ) (d : Fin n → ℕ)
    {X P : Scheme.{u}} [IsIntegral X]
    (q : X ⟶ P) [IsFinite q]
    (a : ∀ i, P ⟶ Proj
      (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) R))
    (haff : ∀ (V : ∀ i, (Proj
      (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) R)).Opens),
      (∀ i, IsAffineOpen (V i)) → IsAffineOpen (⨅ i, a i ⁻¹ᵁ V i)) :
    ∃ A : CartierAtlas X X, Nonempty (CartierAffineSectionCover A X) := by
  classical
  let G i := MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) R
  let j i := q ≫ a i
  let v (i : Fin n) (l : Fin (d i + 1)) : G i 1 :=
    ⟨MvPolynomial.X l, MvPolynomial.isHomogeneous_X R l⟩
  have hcover : ∀ i (x : X), ∃ l, j i x ∈ Proj.basicOpen (G i) (v i l : _) := by
    intro i x
    have htop := Proj.iSup_basicOpen_eq_top' (G i)
      (fun l => (v i l : MvPolynomial (Fin (d i + 1)) R))
      (fun l => ⟨1, (v i l).2⟩)
      (mvPolynomial_degree_zero_adjoin_variables R (Fin (d i + 1)))
    apply Opens.mem_iSup.mp
    rw [htop]
    trivial
  choose idx hidx using hcover
  let c (i : Fin n) (x : X) := v i (idx i x)
  let gen i z := proj_coordinate_generic_of_point (G i) (j i) (c i z) z (hidx i z)
  let r (i : Fin n) (t z : X) : X.functionFieldˣ := Units.mk0
    (pulledProjCoordinateRatio (G i) (j i) (c i t) (c i z) (gen i z))
    (pulled_proj_coordinate_ratio_ne_zero (G i) (j i) (c i t) (c i z)
      (gen i t) (gen i z))
  let V (z : X) (i : Fin n) := Proj.basicOpen (G i) (c i z : _)
  let U z : X.Opens := q ⁻¹ᵁ (⨅ i, a i ⁻¹ᵁ V z i)
  have hU (z x : X) : x ∈ U z ↔ ∀ i, j i x ∈ V z i := by
    change q x ∈ (↑(⨅ i, a i ⁻¹ᵁ V z i) : Set P) ↔ _
    simp only [Opens.coe_iInf, Set.mem_iInter, Scheme.Hom.coe_preimage, Set.mem_preimage]
    rfl
  have haffU : ∀ z, IsAffineOpen (U z) := by
    intro z
    exact (haff (V z) (fun i =>
      Proj.isAffineOpen_basicOpen (G i) (c i z : MvPolynomial (Fin (d i + 1)) R)
        (c i z).2 Nat.zero_lt_one)).preimage q
  let A : CartierAtlas X X := {
    chart := U
    affine := haffU
    nonempty z := ⟨z, (hU z z).mpr (fun i => hidx i z)⟩
    covers z := ⟨z, (hU z z).mpr (fun i => hidx i z)⟩
    equation z := ∏ i, r i (genericPoint X) z
    transition := by
      intro z w x hz hw
      have hz' := (hU z x).mp hz
      have hw' := (hU w x).mp hw
      have hu (i : Fin n) : IsUnit
          (projCoordinateRatioStalk (G i) (c i z) (c i w) (j i x) (hw' i)) :=
        (proj_coordinate_ratio_stalk_unit_iff (G i) (c i z) (c i w)
          (j i x) (hw' i)).mpr (hz' i)
      let u i : (X.presheaf.stalk x)ˣ := Units.map
        ((j i).stalkMap x).hom.toMonoidHom (hu i).unit
      refine ⟨∏ i, u i, ?_⟩
      apply Units.ext
      simp only [Units.val_mul, Units.coe_map, Units.coe_prod, map_prod]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      change algebraMap (X.presheaf.stalk x) X.functionField
        (((j i).stalkMap x).hom ((hu i).unit : _)) *
        pulledProjCoordinateRatio (G i) (j i) (c i (genericPoint X)) (c i z)
          (gen i z) = _
      rw [IsUnit.unit_spec,
        pulled_proj_coordinate_ratio_local (G i) (j i) (c i z) (c i w)
          (gen i w) x (hw' i), mul_comm]
      exact pulled_proj_coordinate_ratio_mul (G i) (j i)
        (c i (genericPoint X)) (c i z) (c i w) (gen i z) (gen i w) }
  let mult (t : X) : X.functionFieldˣ := ∏ i, r i t (genericPoint X)
  let E (t : X) := A.rationalTwist (mult t)
  have heq (t z : X) : (E t).equation z = ∏ i, r i t z := by
    change ((∏ i, r i t (genericPoint X)) *
      (∏ i, r i (genericPoint X) z) : X.functionFieldˣ) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    apply Units.ext
    exact pulled_proj_coordinate_ratio_mul (G i) (j i)
      (c i t) (c i (genericPoint X)) (c i z) (gen i (genericPoint X)) (gen i z)
  let loc (t z : X) (x : X) (hx : x ∈ U z) (i : Fin n) : X.presheaf.stalk x :=
    ((j i).stalkMap x).hom
      (projCoordinateRatioStalk (G i) (c i t) (c i z) (j i x) ((hU z x).mp hx i))
  have hreg (t z : X) (x : X) (hx : x ∈ U z) :
      algebraMap (X.presheaf.stalk x) X.functionField (∏ i, loc t z x hx i) =
        ((E t).equation z : X.functionField) := by
    rw [heq, Units.coe_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact pulled_proj_coordinate_ratio_local (G i) (j i) (c i t) (c i z)
      (gen i z) x ((hU z x).mp hx i)
  have heff : ∀ t, (E t).Effective := by
    intro t z x hx
    exact ⟨_, hreg t z x hx⟩
  have hcomp (t : X) : (⟨(E t).vanishingSupportᶜ,
      (cartierAtlas_vanishingSupport_isClosed X (E t)).isOpen_compl⟩ : X.Opens) = U t := by
    ext x
    obtain ⟨z, hz⟩ := A.covers x
    change x ∉ (E t).vanishingSupport ↔ x ∈ U t
    rw [cartierAtlas_support_eq_on_chart X (E t) z x hz]
    simp only [not_not]
    rw [rationalUnitAt_regular_iff X x ((E t).equation z) _ (hreg t z x hz),
      IsUnit.prod_univ_iff, hU]
    apply forall_congr'
    intro i
    dsimp [loc]
    rw [isUnit_map_iff ((j i).stalkMap x).hom,
      proj_coordinate_ratio_stalk_unit_iff (G i) (c i t) (c i z) (j i x)
        ((hU z x).mp hz i)]
    rfl
  refine ⟨A, ⟨{ multiplier := mult, effective := heff, affine := ?_, covers := ?_ }⟩⟩
  · intro t
    rw [hcomp t]
    exact haffU t
  · intro x
    have hx : x ∈ U x := (hU x x).mpr (fun i => hidx i x)
    rw [← hcomp x] at hx
    exact ⟨x, hx⟩

end
end Negativity
