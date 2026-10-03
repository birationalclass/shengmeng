module

public import Negativity.CartierOpenRestriction
public import Negativity.NegativeActualCenter
public import Negativity.StrictTransform
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_weil_cycle_pushforward_isWeil
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (D : AlgebraicCycle X ℝ) (hD : AlgebraicCycle.IsWeilDivisor D) :
    AlgebraicCycle.IsWeilDivisor
      (AlgebraicCycle.map f Order.coheight Order.coheight D) := by
  intro y hn
  by_contra hy
  change Order.coheight y ≠ 1 at hy
  apply hn
  change (∑ᶠ x ∈ f.base ⁻¹' {y},
    D x * (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight x : ℝ)) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  by_cases hxy : f x = y
  · by_cases hx : D x = 0
    · simp [hx]
    · have hdrop : Order.coheight x ≠ Order.coheight (f x) := by
        rw [hD.coheight_eq_one hx, hxy]
        exact Ne.symm hy
      rw [scheme_mapCoeff_zero_of_drop f Order.coheight Order.coheight x hdrop]
      simp
  · simp [Set.mem_preimage, Set.mem_singleton_iff, hxy]

/-- Final theorem: actual effective Weil pushforward remains effective
after restricting the actual proper birational morphism and the same
finite real Cartier presentation to an actual nonempty target open.
The fixed Cartier restriction and all coefficient/degree comparisons are
proved from actual open stalks and codimension-one isomorphisms. -/
theorem actual_real_cartier_pushforward_effective_on_open
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (hp : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (r t)))) :
    letI : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
      ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›))
    CycleEffective (AlgebraicCycle.map (f ∣_ U) Order.coheight Order.coheight
      (∑ t, (actualCartierPullback (f ⁻¹ᵁ U).ι (A t)).weightedWeilCycle
        (normalStalks_restrict X (f ⁻¹ᵁ U) hnX) (r t))) := by
  classical
  let : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
    ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›))
  let hnV := normalStalks_restrict X (f ⁻¹ᵁ U) hnX
  let hnU := normalStalks_restrict Y U hnY
  let D := ∑ t, (A t).weightedWeilCycle hnX (r t)
  let DV := ∑ t, (actualCartierPullback (f ⁻¹ᵁ U).ι (A t)).weightedWeilCycle hnV (r t)
  have hDV : AlgebraicCycle.IsWeilDivisor DV := by
    simpa [DV] using cartierAtlas_real_sum_isWeilDivisor (f ⁻¹ᵁ U).toScheme hnV
      (fun t => actualCartierPullback (f ⁻¹ᵁ U).ι (A t)) r Finset.univ
  have hlocal := birationalMorphism_restrict f hf U
  intro y
  by_cases hy : Order.coheight y = 1
  · let z := geometricStrictTransform hnU (f ∣_ U) hlocal ⟨y, hy⟩
    have hzy : (f ∣_ U) z = y := geometricStrictTransform_image hnU (f ∣_ U) hlocal ⟨y, hy⟩
    have hxy : f ((f ⁻¹ᵁ U).ι z) = U.ι y := by
      change f z.1.1 = y.1
      exact (morphismRestrict_base_coe f U (z : (f ⁻¹ᵁ U).toScheme)).symm.trans
        (congrArg Subtype.val hzy)
    have hyY : Order.coheight (U.ι y) = 1 :=
      (coheight_eq_of_isOpenImmersion U.ι).trans hy
    have := hnY (U.ι y)
    obtain ⟨W, hyW, hiW⟩ := proper_birational_isIso_near_codimensionOne f hf (U.ι y) hyY
    have : IsIso (f ∣_ W) := hiW
    have heq := actual_cycle_coefficient_over_isomorphism_open f W
      ((f ⁻¹ᵁ U).ι z) (by rwa [hxy]) D
    have hpos : 0 ≤ D ((f ⁻¹ᵁ U).ι z) := by
      rw [← heq]
      exact hp (f ((f ⁻¹ᵁ U).ι z))
    rw [scheme_cycle_strictTransform_coefficient hnU (f ∣_ U) hlocal DV ⟨y, hy⟩]
    change 0 ≤ DV z
    rw [actual_real_cartier_open_restriction_cycle hnX (f ⁻¹ᵁ U) A r z]
    exact hpos
  · have hz : AlgebraicCycle.map (f ∣_ U) Order.coheight Order.coheight DV y = 0 := by
      by_contra hne
      exact hy ((actual_weil_cycle_pushforward_isWeil (f ∣_ U) DV hDV).coheight_eq_one hne)
    rw [hz]

end
end Negativity
