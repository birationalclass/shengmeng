module

public import Negativity.RationalCone
public import Negativity.CartierCombinations
public import Negativity.CartierPushPull
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false

/-- An effective real combination of genuine Cartier presentations has
a nonnegative decomposition into genuine integral Cartier combinations
whose actual Weil coefficients are nonnegative. All zero prime
coefficients stay zero. No Cartier combination or coefficient identity
is supplied as a hypothesis. Local regularity of the resulting Cartier
equations is a further normal-domain extension theorem. -/
theorem exists_realCartier_nonnegative_weil_decomposition (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, c t * ((A t).coefficient hn x : ℝ)) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (B : J → CartierAtlas X X),
      (∀ j, 0 ≤ w j) ∧ (∀ j x, 0 ≤ (B j).coefficient hn x) ∧
      (∀ j x, (∑ t, c t * ((A t).coefficient hn x : ℝ)) = 0 →
        (B j).coefficient hn x = 0) ∧
      (∑ j, (B j).weightedWeilCycle hn (w j)) =
        ∑ t, (A t).weightedWeilCycle hn (c t) := by
  classical
  let S : Set X := ⋃ t, ((A t).weilCycle hn).support
  have hS : S.Finite := Set.finite_iUnion (fun t => cartierAtlas_weilCycle_finite_support X hn (A t))
  let : Fintype S := hS.fintype
  let M (t : τ) (x : S) : ℚ := (A t).coefficient hn x.1
  have hm : ∀ x : S, 0 ≤ rationalCoefficientMap M c x := by
    intro x
    simpa [rationalCoefficientMap, M] using he x.1
  obtain ⟨J, hJ, w, z, hw, hzpos, hzzero, hsum⟩ :=
    effective_integral_coefficient_decomposition M c hm
  let : Fintype J := hJ
  choose B hB using fun j => exists_cartierAtlas_integralCombination_coefficients X hn A (z j)
  have hzoutside (x : X) (hx : x ∉ S) (t : τ) : (A t).coefficient hn x = 0 := by
    by_contra h
    apply hx
    exact Set.mem_iUnion.mpr ⟨t, h⟩
  have hcoeff (j : J) (x : S) : ((B j).coefficient hn x.1 : ℝ) =
      rationalCoefficientMap M (fun t => (z j t : ℝ)) x := by
    rw [hB]
    simp [rationalCoefficientMap, M]
  have houtside (j : J) (x : X) (hx : x ∉ S) : (B j).coefficient hn x = 0 := by
    rw [hB]
    simp [hzoutside x hx]
  refine ⟨J, hJ, w, B, hw, ?_, ?_, ?_⟩
  · intro j x
    by_cases hx : x ∈ S
    · have hp := hzpos j ⟨x, hx⟩
      rw [← hcoeff j ⟨x, hx⟩] at hp
      exact_mod_cast hp
    · rw [houtside j x hx]
  · intro j x hx0
    by_cases hx : x ∈ S
    · have hz := hzzero j ⟨x, hx⟩ (by simpa [rationalCoefficientMap, M] using hx0)
      rw [← hcoeff j ⟨x, hx⟩] at hz
      exact_mod_cast hz
    · exact houtside j x hx
  · ext x
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    change (∑ j, w j * ((B j).coefficient hn x : ℝ)) =
      ∑ t, c t * ((A t).coefficient hn x : ℝ)
    simp_rw [hB, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hs := congrFun hsum t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [hs]

end Negativity
