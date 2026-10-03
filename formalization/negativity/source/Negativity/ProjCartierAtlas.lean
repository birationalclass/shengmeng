module

public import Negativity.ProjCoordinatePullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {R : Type u} {σ : Type*} [CommRing R] [SetLike σ R]
  [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {X : Scheme.{u}} [IsIntegral X]

theorem proj_coordinate_generic_of_point
    (j : X ⟶ Proj 𝒜) {d : ℕ} (a : 𝒜 d) (x : X)
    (hx : j x ∈ Proj.basicOpen 𝒜 (a : R)) :
    j (genericPoint X) ∈ Proj.basicOpen 𝒜 (a : R) := by
  exact ((genericPoint_spec X).mem_open_set_iff
    (j ⁻¹ᵁ Proj.basicOpen 𝒜 (a : R)).isOpen).mpr ⟨x, trivial, hx⟩

/-- Final theorem: actual Cartier coordinate equations are constructed
along an actual closed embedding into Proj. A positive-degree homogeneous
coordinate nonvanishing at each point supplies affine charts. Genuine
Proj stalk ratios give unit transitions; no Cartier atlas or transition
identity is a geometric input. -/
theorem exists_actual_proj_cartier_atlas
    (j : X ⟶ Proj 𝒜) [IsClosedImmersion j] {d : ℕ} (hd : 0 < d)
    (c : X → 𝒜 d) (hc : ∀ x : X, j x ∈ Proj.basicOpen 𝒜 (c x : R)) :
    ∃ A : CartierAtlas X X, ∀ z : X,
      A.chart z = j ⁻¹ᵁ Proj.basicOpen 𝒜 (c z : R) ∧
      (A.equation z : X.functionField) =
        pulledProjCoordinateRatio 𝒜 j (c (genericPoint X)) (c z)
          (proj_coordinate_generic_of_point 𝒜 j (c z) z (hc z)) := by
  classical
  let gen (z : X) := proj_coordinate_generic_of_point 𝒜 j (c z) z (hc z)
  let a := c (genericPoint X)
  have ha : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (a : R) := hc (genericPoint X)
  let eqs (z : X) : X.functionFieldˣ := Units.mk0
    (pulledProjCoordinateRatio 𝒜 j a (c z) (gen z))
    (pulled_proj_coordinate_ratio_ne_zero 𝒜 j a (c z) ha (gen z))
  let A : CartierAtlas X X := {
    chart z := j ⁻¹ᵁ Proj.basicOpen 𝒜 (c z : R)
    affine z := (Proj.isAffineOpen_basicOpen 𝒜 (c z : R) (c z).2 hd).preimage j
    nonempty z := ⟨z, hc z⟩
    covers z := ⟨z, hc z⟩
    equation := eqs
    transition := by
      intro i l x hi hl
      have hu := (proj_coordinate_ratio_stalk_unit_iff 𝒜 (c i) (c l) (j x) hl).mpr hi
      obtain ⟨v, hv⟩ := hu
      refine ⟨Units.map (j.stalkMap x).hom.toMonoidHom v, ?_⟩
      apply Units.ext
      simp only [Units.val_mul, Units.coe_map]
      change algebraMap (X.presheaf.stalk x) X.functionField
        ((j.stalkMap x).hom (v : (Proj 𝒜).presheaf.stalk (j x))) *
        pulledProjCoordinateRatio 𝒜 j a (c i) (gen i) =
          pulledProjCoordinateRatio 𝒜 j a (c l) (gen l)
      rw [hv, pulled_proj_coordinate_ratio_local 𝒜 j (c i) (c l) (gen l) x hl, mul_comm]
      exact pulled_proj_coordinate_ratio_mul 𝒜 j a (c i) (c l) (gen i) (gen l) }
  exact ⟨A, fun _ => ⟨rfl, rfl⟩⟩

end
end Negativity
