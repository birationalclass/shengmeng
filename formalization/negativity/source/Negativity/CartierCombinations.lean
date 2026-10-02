module

public import Negativity.CartierSupport
public import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- The actual local rational order, viewed as a homomorphism from
multiplication of rational equations to addition of signed orders. -/
noncomputable def dvrRationalOrderHom (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Kˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (DvrRationalOrder R K a)
  map_one' := by
    change DvrRationalOrder R K 1 = 0
    simpa using dvr_rationalOrder_unit R K 1
  map_mul' a b := dvr_rationalOrder_mul R K a b

theorem dvr_rationalOrder_zpow (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (n : ℤ) :
    DvrRationalOrder R K (a ^ n) = n * DvrRationalOrder R K a := by
  have h := congrArg Multiplicative.toAdd (map_zpow (dvrRationalOrderHom R K) a n)
  simpa [dvrRationalOrderHom] using h

theorem dvr_rationalOrder_prod (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {τ : Type*} (s : Finset τ) (a : τ → Kˣ) :
    DvrRationalOrder R K (∏ t ∈ s, a t) = ∑ t ∈ s, DvrRationalOrder R K (a t) := by
  have h := congrArg Multiplicative.toAdd (map_prod (dvrRationalOrderHom R K) a s)
  change DvrRationalOrder R K (∏ t ∈ s, a t) =
    Multiplicative.toAdd (∏ t ∈ s, Multiplicative.ofAdd (DvrRationalOrder R K (a t))) at h
  exact h

/-- Construct a genuine integral combination of Cartier presentations.
Charts are refined to affine neighborhoods, and regular unit transitions
are constructed as products of integral powers of the original units. -/
theorem exists_cartierAtlas_integralCombination (X : Scheme) [IsIntegral X]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℤ) :
    ∃ B : CartierAtlas X X, ∀ z : X,
      z ∈ B.chart z ∧
      (∀ t, B.chart z ≤ (A t).chart ((A t).covers z).choose) ∧
      B.equation z = ∏ t, (A t).equation ((A t).covers z).choose ^ c t := by
  classical
  let U (z : X) : X.Opens := ⨅ t, (A t).chart ((A t).covers z).choose
  have hzU (z : X) : z ∈ U z := by
    change z ∈ (↑(⨅ t, (A t).chart ((A t).covers z).choose) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun t => ((A t).covers z).choose_spec)
  have ha (z : X) : ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧ V ≤ U z := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hzU z) (U z).isOpen
    exact ⟨V, hV, hzV, hle⟩
  choose V hV hzV hle using ha
  have hc (z : X) (t : τ) : V z ≤ (A t).chart ((A t).covers z).choose :=
    (hle z).trans (iInf_le _ t)
  let B : CartierAtlas X X := {
    chart := V
    affine := hV
    nonempty := fun z => ⟨z, hzV z⟩
    covers := fun z => ⟨z, hzV z⟩
    equation := fun z => ∏ t, (A t).equation ((A t).covers z).choose ^ c t
    transition := by
      intro z w x hz hw
      choose u hu using fun t => (A t).transition _ _ x (hc z t hz) (hc w t hw)
      refine ⟨∏ t, u t ^ c t, ?_⟩
      simp only [map_prod, map_zpow]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro t _
      rw [← mul_zpow, hu t] }
  exact ⟨B, fun z => ⟨hzV z, hc z, rfl⟩⟩

/-- The integral combination constructed from actual Cartier local
equations has exactly the corresponding sum of actual Weil coefficients.
This does not assume the resulting Cartier equation is effective. -/
theorem exists_cartierAtlas_integralCombination_coefficients (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℤ) :
    ∃ B : CartierAtlas X X, ∀ x : X,
      B.coefficient hn x = ∑ t, c t * (A t).coefficient hn x := by
  classical
  obtain ⟨B, hB⟩ := exists_cartierAtlas_integralCombination X A c
  refine ⟨B, ?_⟩
  intro x
  by_cases hx : Order.coheight x = 1
  · rw [cartierAtlas_coefficient_eq X hn B x x hx (hB x).1, (hB x).2.2]
    have := hn x
    have := normal_codimensionOne_stalk_isDVR X x hx
    unfold schemeRationalOrder
    rw [dvr_rationalOrder_prod]
    apply Finset.sum_congr rfl
    intro t _
    rw [dvr_rationalOrder_zpow, cartierAtlas_coefficient_eq X hn (A t) _ x hx
      ((A t).covers x).choose_spec]
    rfl
  · simp [CartierAtlas.coefficient, hx]

end Negativity
