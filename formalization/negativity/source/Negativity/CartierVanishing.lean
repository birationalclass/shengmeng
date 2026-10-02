module

public import Negativity.CartierEffectivity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- A rational equation which is a unit in an actual local ring is
represented by a unit section on an affine neighborhood of that point. -/
theorem rationalUnitAt_exists_affine_unit_section (X : Scheme) [IsIntegral X]
    (x : X) (a : X.functionFieldˣ) (ha : RationalUnitAt X x a) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U)
      (r : Γ(X, U)), IsUnit r ∧
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx r) =
        (a : X.functionField) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨V, hxV, r, hr⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  let s : Γ(X, W) := X.presheaf.map (homOfLE hWV).op r
  have hs : X.presheaf.germ W x hxW s = (u : X.presheaf.stalk x) := by
    exact (X.presheaf.germ_res_apply (homOfLE hWV) x hxW r).trans hr
  have hxB : x ∈ X.basicOpen s := by
    rw [Scheme.mem_basicOpen X s x hxW, hs]
    exact u.isUnit
  let t : Γ(X, X.basicOpen s) := X.presheaf.map (X.basicOpen_le s).hom.op s
  have ht : X.presheaf.germ (X.basicOpen s) x hxB t = (u : X.presheaf.stalk x) := by
    exact (X.presheaf.germ_res_apply (X.basicOpen_le s).hom x hxB s).trans hs
  refine ⟨X.basicOpen s, hW.basicOpen s, hxB, t,
    X.toRingedSpace.isUnit_res_basicOpen s, ?_⟩
  rw [ht]
  exact congrArg Units.val hu

/-- The locus where a rational equation is a regular unit is open. -/
theorem rationalUnitAt_isOpen (X : Scheme) [IsIntegral X] (a : X.functionFieldˣ) :
    IsOpen {x : X | RationalUnitAt X x a} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨U, hU, hxU, r, hr, he⟩ := rationalUnitAt_exists_affine_unit_section X x a hx
  have : Nonempty U := ⟨x, hxU⟩
  have he' : X.germToFunctionField U r = (a : X.functionField) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X hxU r).symm.trans he
  refine ⟨U, ?_, U.isOpen, hxU⟩
  intro y hy
  obtain ⟨u, hu⟩ := hr.map (X.presheaf.germ U y hy).hom
  refine ⟨u, Units.ext ?_⟩
  change algebraMap (X.presheaf.stalk y) X.functionField (u : X.presheaf.stalk y) = _
  rw [hu]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X hy r).trans he'

/-- The actual Cartier support is closed in every codimension. -/
theorem cartierAtlas_vanishingSupport_isClosed (X : Scheme) [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) : IsClosed A.vanishingSupport := by
  apply isOpen_compl_iff.mp
  have he : A.vanishingSupportᶜ =
      ⋃ i, (A.chart i : Set X) ∩ {x | RationalUnitAt X x (A.equation i)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := A.covers x
      refine ⟨i, hi, ?_⟩
      rw [cartierAtlas_support_eq_on_chart X A i x hi] at hx
      exact Classical.not_not.mp hx
    · rintro ⟨i, hi, hu⟩
      rw [cartierAtlas_support_eq_on_chart X A i x hi]
      exact not_not_intro hu
  rw [he]
  exact isOpen_iUnion (fun i => (A.chart i).isOpen.inter (rationalUnitAt_isOpen X (A.equation i)))

/-- A rational equation with zero order at every height-one point of an
affine normal open is a unit at every point of that open. Both the equation
and its inverse extend by the proved normal-domain theorem. -/
theorem normal_affine_rationalUnitAt_of_orders_zero (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (a : X.functionFieldˣ)
    (hzero : ∀ (y : X), y ∈ U → ∀ hc : Order.coheight y = 1,
      schemeRationalOrder X hn y hc a = 0) (x : X) (hx : x ∈ U) :
    RationalUnitAt X x a := by
  obtain ⟨r, hr⟩ := normal_affine_rational_regular X hn U hU a
    (fun y hy hc => by rw [hzero y hy hc])
  obtain ⟨s, hs⟩ := normal_affine_rational_regular X hn U hU a⁻¹ (by
    intro y hy hc
    have := hn y
    have := normal_codimensionOne_stalk_isDVR X y hc
    change 0 ≤ DvrRationalOrder (X.presheaf.stalk y) X.functionField a⁻¹
    have he := dvr_rationalOrder_zpow (X.presheaf.stalk y) X.functionField a (-1)
    rw [zpow_neg_one, neg_one_mul] at he
    rw [he]
    change 0 ≤ -schemeRationalOrder X hn y hc a
    rw [hzero y hy hc]
    rfl)
  let r' := X.presheaf.germ U x hx r
  let s' := X.presheaf.germ U x hx s
  have hr' : algebraMap (X.presheaf.stalk x) X.functionField r' = (a : X.functionField) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X hx r).trans hr
  have hs' : algebraMap (X.presheaf.stalk x) X.functionField s' = (a⁻¹ : X.functionFieldˣ) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X hx s).trans hs
  have hmul : r' * s' = 1 := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, hr', hs', map_one]
    simp
  let u : (X.presheaf.stalk x)ˣ := ⟨r', s', hmul, by rw [mul_comm]; exact hmul⟩
  exact ⟨u, Units.ext hr'⟩

/-- On a normal locally Noetherian integral scheme, the actual Cartier
support in all codimensions is the closure of its actual nonzero Weil
coefficients. In particular this includes exceptional higher-codimension
points, rather than identifying support with a coefficient index set. -/
theorem cartierAtlas_vanishingSupport_eq_closure_weilSupport (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) :
    A.vanishingSupport = closure (A.weilCycle hn).support := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxcl
    obtain ⟨i, hi⟩ := A.covers x
    let W : X.Opens := A.chart i ⊓
      ⟨(closure (A.weilCycle hn).support)ᶜ, isClosed_closure.isOpen_compl⟩
    have hxW : x ∈ W := ⟨hi, hxcl⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    have : Nonempty V := ⟨x, hxV⟩
    have hu : RationalUnitAt X x (A.equation i) :=
      normal_affine_rationalUnitAt_of_orders_zero X hn V hV (A.equation i) (by
        intro y hy hc
        have hz : A.coefficient hn y = 0 := by
          by_contra hyc
          have hym : y ∈ (A.weilCycle hn).support := hyc
          exact ((hVW hy).2) (subset_closure hym)
        rw [cartierAtlas_coefficient_eq X hn A i y hc (hVW hy).1] at hz
        exact hz) x hxV
    exact (cartierAtlas_support_eq_on_chart X A i x hi).mp hx hu
  · apply closure_minimal ?_ (cartierAtlas_vanishingSupport_isClosed X A)
    intro x hx
    change A.coefficient hn x ≠ 0 at hx
    have hc : Order.coheight x = 1 := by
      by_contra h
      exact hx (by simp [CartierAtlas.coefficient, h])
    obtain ⟨i, hi⟩ := A.covers x
    rw [cartierAtlas_support_eq_on_chart X A i x hi]
    rintro ⟨u, hu⟩
    rw [cartierAtlas_coefficient_eq X hn A i x hc hi] at hx
    have := hn x
    have := normal_codimensionOne_stalk_isDVR X x hc
    unfold schemeRationalOrder at hx
    rw [← hu] at hx
    exact hx (dvr_rationalOrder_unit (X.presheaf.stalk x) X.functionField u)

/-- The geometric support of a nonnegative real sum of actual effective
Cartier divisors is the union of the Cartier supports with positive weights.
The left side is the closure of the actual real Weil cycle support. -/
theorem effective_cartier_real_sum_support (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hA : ∀ t, (A t).Effective) :
    closure (∑ t, (A t).weightedWeilCycle hn (c t)).support =
      ⋃ t : {t : τ // 0 < c t}, (A t.1).vanishingSupport := by
  classical
  have heff (t : τ) (x : X) : 0 ≤ (A t).coefficient hn x :=
    effective_cartierAtlas_weil_nonneg X hn (A t) (hA t) x
  have hs : (∑ t, (A t).weightedWeilCycle hn (c t)).support =
      ⋃ t : {t : τ // 0 < c t}, ((A t.1).weilCycle hn).support := by
    ext x
    simp only [Set.mem_iUnion]
    change ((∑ t, (A t).weightedWeilCycle hn (c t)) x ≠ 0) ↔ _
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    change (∑ t, c t * ((A t).coefficient hn x : ℝ)) ≠ 0 ↔ _
    have hp : ∀ t ∈ Finset.univ, 0 ≤ c t * ((A t).coefficient hn x : ℝ) := by
      intro t _
      apply mul_nonneg (hc t)
      exact_mod_cast heff t x
    constructor
    · intro hne
      have hpos : 0 < ∑ t, c t * ((A t).coefficient hn x : ℝ) :=
        lt_of_le_of_ne (Finset.sum_nonneg hp) hne.symm
      obtain ⟨t, _, ht⟩ := (Finset.sum_pos_iff_of_nonneg hp).mp hpos
      have hv : 0 ≤ ((A t).coefficient hn x : ℝ) := by exact_mod_cast heff t x
      have hct : 0 < c t := by nlinarith [hv]
      refine ⟨⟨t, hct⟩, ?_⟩
      change (A t).coefficient hn x ≠ 0
      intro hz
      simp [hz] at ht
    · rintro ⟨t, ht⟩
      change (A t.1).coefficient hn x ≠ 0 at ht
      have hz : 0 < (A t.1).coefficient hn x := lt_of_le_of_ne (heff t.1 x) ht.symm
      have hpos : 0 < ∑ t, c t * ((A t).coefficient hn x : ℝ) :=
        (Finset.sum_pos_iff_of_nonneg hp).mpr
          ⟨t.1, Finset.mem_univ _, mul_pos t.2 (Int.cast_pos.mpr hz)⟩
      exact ne_of_gt hpos
  rw [hs, closure_iUnion_of_finite]
  apply Set.iUnion_congr
  intro t
  exact (cartierAtlas_vanishingSupport_eq_closure_weilSupport X hn (A t.1)).symm

/-- Pullback of nonnegative real sums of actual effective Cartier divisors
has the genuine inverse-image geometric support. The effective pullbacks
and their local rational equations are constructed from the scheme map. -/
theorem exists_effective_real_sum_pullback_support {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsDominant f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas Y ι) (c : τ → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hA : ∀ t, (A t).Effective) :
    ∃ B : τ → CartierAtlas X X, (∀ t, (B t).Effective) ∧
      closure (∑ t, (B t).weightedWeilCycle hnX (c t)).support =
        f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnY (c t)).support ∧
      ∀ t z, (B t).equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
        ((A t).equation ((A t).covers (f z)).choose) := by
  classical
  choose B hB hs heq using fun t => exists_effective_cartierAtlas_pullback_support f (A t) (hA t)
  refine ⟨B, hB, ?_, heq⟩
  rw [effective_cartier_real_sum_support X hnX B c hc hB,
    effective_cartier_real_sum_support Y hnY A c hc hA]
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage]
  simp_rw [hs, Set.mem_preimage]

/-- An arbitrary effective real Weil combination of genuine Cartier
presentations has a constructed effective Cartier decomposition whose
actual pullback has inverse-image geometric support. The conclusion
retains the decomposition and pullback equations; it does not identify
this pullback with separately supplied pullback data for the original
presentation or assert an upstairs fiber dichotomy. -/
theorem exists_realCartier_decomposition_support_pullback {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsDominant f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas Y ι) (c : τ → ℝ)
    (he : ∀ y : Y, 0 ≤ ∑ t, c t * ((A t).coefficient hnY y : ℝ)) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ)
      (B : J → CartierAtlas Y Y) (B' : J → CartierAtlas X X),
      (∀ j, 0 ≤ w j) ∧ (∀ j, (B j).Effective) ∧ (∀ j, (B' j).Effective) ∧
      (∑ j, (B j).weightedWeilCycle hnY (w j)) =
        ∑ t, (A t).weightedWeilCycle hnY (c t) ∧
      closure (∑ j, (B' j).weightedWeilCycle hnX (w j)).support =
        f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnY (c t)).support ∧
      ∀ j z, (B' j).equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
        ((B j).equation ((B j).covers (f z)).choose) := by
  classical
  obtain ⟨J, hJ, w, B, hw, hB, _, hsum⟩ :=
    exists_realCartier_effective_weil_decomposition Y hnY A c he
  let : Fintype J := hJ
  obtain ⟨B', hB', hs, heq⟩ :=
    exists_effective_real_sum_pullback_support hnX hnY f B w hw hB
  rw [hsum] at hs
  exact ⟨J, hJ, w, B, B', hw, hB, hB', hsum, hs, heq⟩

end Negativity
