module

public import Negativity.CartierPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false

/-- For actual Weil cycles, proper birational geometry supplies the unique
codimension-one preimage and its multiplicity one. Only agreement of the
two given cycles at these points is required in this general cycle lemma. -/
theorem proper_birational_weil_cycle_pushforward {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    {R : Type*} [Semiring R]
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (D : AlgebraicCycle Y R) (E : AlgebraicCycle X R)
    (hD : AlgebraicCycle.IsWeilDivisor D) (hE : AlgebraicCycle.IsWeilDivisor E)
    (hcoeff : ∀ x : X, Order.coheight (f x) = 1 → E x = D (f x)) :
    AlgebraicCycle.map f Order.coheight Order.coheight E = D := by
  classical
  ext y
  change (∑ᶠ x ∈ f.base ⁻¹' {y}, E x *
    (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight x : R)) = D y
  by_cases hy : Order.coheight y = 1
  · have := hnY y
    obtain ⟨x, hxy, hstalk, hx, huniq⟩ :=
      proper_birational_codimensionOne_unique_preimage f hf y hy
    have : IsIso (f.stalkMap x) := hstalk
    have hsingle : ∀ z : X, z ≠ x →
        (∑ᶠ (_ : z ∈ f.base ⁻¹' {y}), E z *
          (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight z : R)) = 0 := by
      intro z hz
      have hzy : f z ≠ y := fun h ↦ hz (huniq z h)
      simp [Set.mem_preimage, Set.mem_singleton_iff, hzy]
    rw [finsum_eq_single _ x hsingle]
    have hweight : Order.coheight x = Order.coheight (f x) := by rw [hx, hxy, hy]
    rw [scheme_mapCoeff_of_same_weight f Order.coheight Order.coheight x hweight,
      scheme_residueDegree_of_stalk_iso]
    simp [hxy, hcoeff x (by rwa [hxy])]
  · have hDy : D y = 0 := by
      by_contra h
      exact hy (hD h)
    rw [hDy]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    by_cases hxy : f x = y
    · by_cases hEx : E x = 0
      · simp [hEx]
      · have hx : Order.coheight x = 1 := hE hEx
        have hdrop : Order.coheight x ≠ Order.coheight (f x) := by
          rw [hx, hxy]
          exact Ne.symm hy
        simp [scheme_mapCoeff_zero_of_drop f Order.coheight Order.coheight x hdrop]
    · simp [Set.mem_preimage, Set.mem_singleton_iff, hxy]

/-- Construct the actual Cartier pullback and prove pushforward-pullback.
The result uses actual Scheme-cycle pushforward and rational equations;
no coefficient equality or push-pull identity is assumed. -/
theorem exists_cartierAtlas_pullback_pushforward {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    {ι : Type*} (A : CartierAtlas Y ι) :
    letI : Surjective f := proper_birational_surjective f hf
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map
          (dominantFunctionFieldMap f : _ →* _) (A.equation (A.covers (f z)).choose)) ∧
      AlgebraicCycle.map f Order.coheight Order.coheight (B.weilCycle hnX) =
        A.weilCycle hnY := by
  classical
  have : Surjective f := proper_birational_surjective f hf
  obtain ⟨B, hB⟩ := exists_cartierAtlas_pullback f A
  refine ⟨B, hB, ?_⟩
  apply proper_birational_weil_cycle_pushforward hnY f hf _ _
    (cartierAtlas_weilCycle_isWeilDivisor Y hnY A)
    (cartierAtlas_weilCycle_isWeilDivisor X hnX B)
  intro x hy
  have := hnY (f x)
  obtain ⟨w, hw, hstalk, hwc, huniq⟩ :=
    proper_birational_codimensionOne_unique_preimage f hf (f x) hy
  have hwx : x = w := huniq x rfl
  have hx : Order.coheight x = 1 := hwx ▸ hwc
  have : IsIso (f.stalkMap x) := hwx ▸ hstalk
  obtain ⟨z, hz⟩ := B.covers x
  obtain ⟨hle, _, heq⟩ := hB z
  change B.coefficient hnX x = A.coefficient hnY (f x)
  rw [cartierAtlas_coefficient_eq X hnX B z x hx hz,
    cartierAtlas_coefficient_eq Y hnY A (A.covers (f z)).choose (f x) hy (hle hz), heq]
  exact dominantFunctionFieldMap_order_of_stalk_iso hnX hnY f x hx hy _

/-- One real multiple of an actual Cartier divisor's Weil cycle. -/
noncomputable def CartierAtlas.weightedWeilCycle {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] {ι : Type*} (A : CartierAtlas X ι)
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (c : ℝ) : AlgebraicCycle X ℝ :=
  (A.weilCycle hn).mapRange (fun n : ℤ ↦ c * (n : ℝ)) (by simp)

/-- Finite real combinations of actual Cartier cycles are Weil divisors. -/
theorem cartierAtlas_real_sum_isWeilDivisor (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} (A : τ → CartierAtlas X ι) (c : τ → ℝ) (s : Finset τ) :
    AlgebraicCycle.IsWeilDivisor (∑ t ∈ s, (A t).weightedWeilCycle hn (c t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (AlgebraicCycle.isWeilDivisor_zero (X := X) (R := ℝ))
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht]
    apply AlgebraicCycle.IsWeilDivisor.add _ ih
    exact (Function.locallyFinsuppWithin.support_mapRange_subset _ _ _).trans
      (cartierAtlas_weilCycle_isWeilDivisor X hn (A t))

/-- Real Cartier push-pull, with each pullback atlas constructed from the
actual scheme morphism. This verifies the finite real-linear-combination
version used in the negativity lemma, with no push-pull input. -/
theorem exists_realCartier_pullback_pushforward {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    {ι τ : Type*} (A : τ → CartierAtlas Y ι) (c : τ → ℝ) (s : Finset τ) :
    letI : Surjective f := proper_birational_surjective f hf
    ∃ B : τ → CartierAtlas X X,
      (∀ t z, (B t).chart z ≤ f ⁻¹ᵁ (A t).chart ((A t).covers (f z)).choose ∧
        z ∈ (B t).chart z ∧ (B t).equation z =
          Units.map (dominantFunctionFieldMap f : _ →* _)
            ((A t).equation ((A t).covers (f z)).choose)) ∧
      AlgebraicCycle.map f Order.coheight Order.coheight
        (∑ t ∈ s, (B t).weightedWeilCycle hnX (c t)) =
          ∑ t ∈ s, (A t).weightedWeilCycle hnY (c t) := by
  classical
  have : Surjective f := proper_birational_surjective f hf
  choose B hB using fun t ↦ exists_cartierAtlas_pullback f (A t)
  refine ⟨B, hB, ?_⟩
  apply proper_birational_weil_cycle_pushforward hnY f hf _ _
    (cartierAtlas_real_sum_isWeilDivisor Y hnY A c s)
    (cartierAtlas_real_sum_isWeilDivisor X hnX B c s)
  intro x hy
  have := hnY (f x)
  obtain ⟨w, hw, hstalk, hwc, huniq⟩ :=
    proper_birational_codimensionOne_unique_preimage f hf (f x) hy
  have hwx : x = w := huniq x rfl
  have hx : Order.coheight x = 1 := hwx ▸ hwc
  have : IsIso (f.stalkMap x) := hwx ▸ hstalk
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨z, hz⟩ := (B t).covers x
  obtain ⟨hle, _, heq⟩ := hB t z
  have hc : (B t).coefficient hnX x = (A t).coefficient hnY (f x) := by
    rw [cartierAtlas_coefficient_eq X hnX (B t) z x hx hz,
      cartierAtlas_coefficient_eq Y hnY (A t) ((A t).covers (f z)).choose
        (f x) hy (hle hz), heq]
    exact dominantFunctionFieldMap_order_of_stalk_iso hnX hnY f x hx hy _
  change c t * ((B t).coefficient hnX x : ℝ) = c t * ((A t).coefficient hnY (f x) : ℝ)
  rw [hc]

/-- Effectivity descends for the constructed real Cartier pullback. The
push-pull identity is proved internally, not an assumption of this theorem. -/
theorem exists_realCartier_effectivity_descent {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    {ι τ : Type*} (A : τ → CartierAtlas Y ι) (c : τ → ℝ) (s : Finset τ) :
    letI : Surjective f := proper_birational_surjective f hf
    ∃ B : τ → CartierAtlas X X,
      (∀ t z, (B t).chart z ≤ f ⁻¹ᵁ (A t).chart ((A t).covers (f z)).choose ∧
        z ∈ (B t).chart z ∧ (B t).equation z =
          Units.map (dominantFunctionFieldMap f : _ →* _)
            ((A t).equation ((A t).covers (f z)).choose)) ∧
      AlgebraicCycle.map f Order.coheight Order.coheight
        (∑ t ∈ s, (B t).weightedWeilCycle hnX (c t)) =
          ∑ t ∈ s, (A t).weightedWeilCycle hnY (c t) ∧
      (CycleEffective (∑ t ∈ s, (B t).weightedWeilCycle hnX (c t)) →
        CycleEffective (∑ t ∈ s, (A t).weightedWeilCycle hnY (c t))) := by
  have : Surjective f := proper_birational_surjective f hf
  obtain ⟨B, hB, hm⟩ := exists_realCartier_pullback_pushforward hnX hnY f hf A c s
  refine ⟨B, hB, hm, ?_⟩
  intro he
  rw [← hm]
  exact scheme_cycle_map_effective f Order.coheight Order.coheight _ he

end Negativity
