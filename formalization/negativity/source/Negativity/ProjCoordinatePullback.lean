module

public import Negativity.ProjCoordinateRatios
public import Negativity.CartierAtlas
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

/-- The actual rational coordinate ratio on an integral scheme mapping
to Proj. It is constructed from a genuine pulled-back regular section. -/
def pulledProjCoordinateRatio (j : X ⟶ Proj 𝒜) {d : ℕ} (a b : 𝒜 d)
    (hb : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (b : R)) : X.functionField := by
  have : Nonempty (j ⁻¹ᵁ Proj.basicOpen 𝒜 (b : R)) := ⟨genericPoint X, hb⟩
  exact X.germToFunctionField (j ⁻¹ᵁ Proj.basicOpen 𝒜 (b : R))
    (j.app (Proj.basicOpen 𝒜 (b : R)) (projCoordinateRatioSection 𝒜 a b))

theorem pulled_proj_coordinate_ratio_local
    (j : X ⟶ Proj 𝒜) {d : ℕ} (a b : 𝒜 d)
    (hb : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (b : R))
    (x : X) (hx : j x ∈ Proj.basicOpen 𝒜 (b : R)) :
    algebraMap (X.presheaf.stalk x) X.functionField
      ((j.stalkMap x).hom (projCoordinateRatioStalk 𝒜 a b (j x) hx)) =
      pulledProjCoordinateRatio 𝒜 j a b hb := by
  have : Nonempty (j ⁻¹ᵁ Proj.basicOpen 𝒜 (b : R)) := ⟨genericPoint X, hb⟩
  rw [← proj_coordinate_ratio_section_germ 𝒜 a b (j x) hx]
  rw [j.germ_stalkMap_apply]
  exact Scheme.algebraMap_germ_eq_germToFunctionField X hx _

theorem pulled_proj_coordinate_ratio_ne_zero
    (j : X ⟶ Proj 𝒜) {d : ℕ} (a b : 𝒜 d)
    (ha : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (a : R))
    (hb : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (b : R)) :
    pulledProjCoordinateRatio 𝒜 j a b hb ≠ 0 := by
  have hu := (proj_coordinate_ratio_stalk_unit_iff 𝒜 a b (j (genericPoint X)) hb).mpr ha
  have : Nonempty (j ⁻¹ᵁ Proj.basicOpen 𝒜 (b : R)) := ⟨genericPoint X, hb⟩
  intro hz
  have hs : j.app (Proj.basicOpen 𝒜 (b : R)) (projCoordinateRatioSection 𝒜 a b) = 0 := by
    apply X.germToFunctionField_injective (j ⁻¹ᵁ Proj.basicOpen 𝒜 (b : R))
    exact hz.trans (map_zero _).symm
  apply (hu.map (j.stalkMap (genericPoint X)).hom).ne_zero
  rw [← proj_coordinate_ratio_section_germ 𝒜 a b (j (genericPoint X)) hb,
    j.germ_stalkMap_apply, hs]
  exact map_zero _

/-- Final theorem: genuine homogeneous coordinate ratios multiply after
pullback to the actual function field, with no dominant-map requirement.
This supplies the local-equation transition identities for the actual
Cartier pullback of O(1) along a closed projective embedding. -/
theorem pulled_proj_coordinate_ratio_mul
    (j : X ⟶ Proj 𝒜) {d : ℕ} (a b c : 𝒜 d)
    (hb : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (b : R))
    (hc : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (c : R)) :
    pulledProjCoordinateRatio 𝒜 j a b hb * pulledProjCoordinateRatio 𝒜 j b c hc =
      pulledProjCoordinateRatio 𝒜 j a c hc := by
  rw [← pulled_proj_coordinate_ratio_local 𝒜 j a b hb (genericPoint X) hb,
    ← pulled_proj_coordinate_ratio_local 𝒜 j b c hc (genericPoint X) hc,
    ← pulled_proj_coordinate_ratio_local 𝒜 j a c hc (genericPoint X) hc,
    ← map_mul, ← map_mul, proj_coordinate_ratio_stalk_mul]

end
end Negativity
