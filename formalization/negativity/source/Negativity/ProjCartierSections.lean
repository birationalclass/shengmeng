module

public import Negativity.ProjCartierAtlas
public import Negativity.CartierAffineSections
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

/-- Final theorem: actual projective coordinate geometry constructs an
actual Cartier affine section cover. Equations, effective coordinate
sections, their actual vanishing supports and their affine nonvanishing
loci are all constructed. No O(1) Cartier atlas, effectivity, support
identity, positivity or affine section-cover data are supplied as inputs. -/
theorem exists_actual_proj_cartier_affine_section_cover
    (j : X ⟶ Proj 𝒜) [IsClosedImmersion j] {d : ℕ} (hd : 0 < d)
    (c : X → 𝒜 d) (hc : ∀ x : X, j x ∈ Proj.basicOpen 𝒜 (c x : R)) :
    ∃ A : CartierAtlas X X, Nonempty (CartierAffineSectionCover A X) := by
  classical
  obtain ⟨A, hA⟩ := exists_actual_proj_cartier_atlas 𝒜 j hd c hc
  let gen (z : X) := proj_coordinate_generic_of_point 𝒜 j (c z) z (hc z)
  let a := c (genericPoint X)
  have ha : j (genericPoint X) ∈ Proj.basicOpen 𝒜 (a : R) := hc (genericPoint X)
  let mult (z : X) : X.functionFieldˣ := Units.mk0
    (pulledProjCoordinateRatio 𝒜 j (c z) a ha)
    (pulled_proj_coordinate_ratio_ne_zero 𝒜 j (c z) a (gen z) ha)
  let E (z : X) := A.rationalTwist (mult z)
  have heq (t i : X) : (E t).equation i = Units.mk0
      (pulledProjCoordinateRatio 𝒜 j (c t) (c i) (gen i))
      (pulled_proj_coordinate_ratio_ne_zero 𝒜 j (c t) (c i) (gen t) (gen i)) := by
    apply Units.ext
    change pulledProjCoordinateRatio 𝒜 j (c t) a ha * (A.equation i : X.functionField) = _
    rw [(hA i).2]
    exact pulled_proj_coordinate_ratio_mul 𝒜 j (c t) a (c i) ha (gen i)
  have hreg (t i : X) (x : X) (hx : x ∈ A.chart i) :
      algebraMap (X.presheaf.stalk x) X.functionField
        ((j.stalkMap x).hom (projCoordinateRatioStalk 𝒜 (c t) (c i) (j x)
          (by rw [(hA i).1] at hx; exact hx))) =
        ((E t).equation i : X.functionField) := by
    rw [heq]
    exact pulled_proj_coordinate_ratio_local 𝒜 j (c t) (c i) (gen i) x
      (by rw [(hA i).1] at hx; exact hx)
  have heff : ∀ t, (E t).Effective := by
    intro t i x hx
    exact ⟨_, hreg t i x hx⟩
  have hcomp (t : X) : (⟨(E t).vanishingSupportᶜ,
      (cartierAtlas_vanishingSupport_isClosed X (E t)).isOpen_compl⟩ : X.Opens) =
      j ⁻¹ᵁ Proj.basicOpen 𝒜 (c t : R) := by
    ext x
    obtain ⟨i, hi⟩ := A.covers x
    have hi' : j x ∈ Proj.basicOpen 𝒜 (c i : R) := by
      rw [(hA i).1] at hi
      exact hi
    have hs : (x ∉ (E t).vanishingSupport) ↔ j x ∈ Proj.basicOpen 𝒜 (c t : R) := by
      rw [cartierAtlas_support_eq_on_chart X (E t) i x hi]
      simp only [not_not]
      rw [rationalUnitAt_regular_iff X x ((E t).equation i) _ (hreg t i x hi),
        isUnit_map_iff (j.stalkMap x).hom,
        proj_coordinate_ratio_stalk_unit_iff 𝒜 (c t) (c i) (j x) hi']
      rfl
    exact hs
  refine ⟨A, ⟨{
    multiplier := mult
    effective := heff
    affine := ?_
    covers := ?_ }⟩⟩
  · intro t
    rw [hcomp t]
    exact (Proj.isAffineOpen_basicOpen 𝒜 (c t : R) (c t).2 hd).preimage j
  · intro x
    refine ⟨x, ?_⟩
    have hx : x ∈ j ⁻¹ᵁ Proj.basicOpen 𝒜 (c x : R) := hc x
    rw [← hcomp x] at hx
    exact hx

end
end Negativity
