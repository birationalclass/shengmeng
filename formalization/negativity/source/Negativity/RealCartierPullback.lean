module

public import Negativity.CartierVanishing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- Actual units in a target stalk pull back to actual units in the source
stalk; their images in the function fields commute with this pullback. -/
theorem dominantFunctionFieldMap_stalk_unit {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (x : X) (u : (Y.presheaf.stalk (f x))ˣ) :
    Units.map (dominantFunctionFieldMap f).toMonoidHom
      (Units.map (algebraMap (Y.presheaf.stalk (f x)) Y.functionField).toMonoidHom u) =
    Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom
      (Units.map (f.stalkMap x).hom.toMonoidHom u) := by
  apply Units.ext
  exact dominantFunctionFieldMap_stalk f x (u : Y.presheaf.stalk (f x))

/-- The coefficient of a constructed Cartier pullback is computed from
any target chart containing the image of the source point. No
codimension assumption is made on that target point. -/
theorem cartierAtlas_pullback_coefficient_eq {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Y) [IsDominant f] {ι : Type*}
    (A : CartierAtlas Y ι) (B : CartierAtlas X X)
    (hB : ∀ z : X, z ∈ B.chart z ∧
      B.equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
        (A.equation (A.covers (f z)).choose))
    (x : X) (hx : Order.coheight x = 1) (i : ι) (hi : f x ∈ A.chart i) :
    B.coefficient hnX x = schemeRationalOrder X hnX x hx
      (Units.map (dominantFunctionFieldMap f : _ →* _) (A.equation i)) := by
  rw [cartierAtlas_coefficient_eq X hnX B x x hx (hB x).1, (hB x).2]
  obtain ⟨u, hu⟩ := A.transition _ i (f x) (A.covers (f x)).choose_spec hi
  have hp :
      Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom
        (Units.map (f.stalkMap x).hom.toMonoidHom u) *
          Units.map (dominantFunctionFieldMap f).toMonoidHom (A.equation (A.covers (f x)).choose) =
        Units.map (dominantFunctionFieldMap f).toMonoidHom (A.equation i) := by
    apply Units.ext
    have hc := congrArg (fun v : Y.functionFieldˣ =>
      dominantFunctionFieldMap f (v : Y.functionField)) hu
    simp only [Units.val_mul, Units.coe_map, map_mul] at hc ⊢
    change dominantFunctionFieldMap f
      (algebraMap (Y.presheaf.stalk (f x)) Y.functionField (u : Y.presheaf.stalk (f x))) *
      dominantFunctionFieldMap f (A.equation (A.covers (f x)).choose : Y.functionField) =
      dominantFunctionFieldMap f (A.equation i : Y.functionField) at hc
    rw [dominantFunctionFieldMap_stalk f x (u : Y.presheaf.stalk (f x))] at hc
    exact hc
  have := hnX x
  have := normal_codimensionOne_stalk_isDVR X x hx
  change DvrRationalOrder (X.presheaf.stalk x) X.functionField
    (Units.map (dominantFunctionFieldMap f).toMonoidHom (A.equation (A.covers (f x)).choose)) =
    DvrRationalOrder (X.presheaf.stalk x) X.functionField
      (Units.map (dominantFunctionFieldMap f).toMonoidHom (A.equation i))
  rw [← hp]
  exact (dvr_rationalOrder_unit_transition (X.presheaf.stalk x) X.functionField
    (Units.map (f.stalkMap x).hom.toMonoidHom u)
    (Units.map (dominantFunctionFieldMap f).toMonoidHom
      (A.equation (A.covers (f x)).choose))).symm

/-- Coefficients of actual products of integral powers of local Cartier
equations are the corresponding integral sums. The product equations
and their chart memberships are retained for subsequent pullback. -/
theorem cartierAtlas_integralCombination_coefficients (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℤ)
    (B : CartierAtlas X X)
    (hB : ∀ x : X, x ∈ B.chart x ∧
      B.equation x = ∏ t, (A t).equation ((A t).covers x).choose ^ c t) :
    ∀ x : X, B.coefficient hn x = ∑ t, c t * (A t).coefficient hn x := by
  classical
  intro x
  by_cases hx : Order.coheight x = 1
  · rw [cartierAtlas_coefficient_eq X hn B x x hx (hB x).1, (hB x).2]
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

/-- Effective integral Cartier combinations retain the actual products
of the original rational equations and an equality in the original
coefficient coordinates. These stronger outputs identify their pullbacks. -/
theorem exists_realCartier_effective_decomposition_equations (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, c t * ((A t).coefficient hn x : ℝ)) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (z : J → τ → ℤ)
      (B : J → CartierAtlas X X),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j • (fun t => (z j t : ℝ))) = c ∧
      (∀ j, (B j).Effective) ∧
      ∀ j x, x ∈ (B j).chart x ∧
        (B j).equation x = ∏ t, (A t).equation ((A t).covers x).choose ^ z j t := by
  classical
  let S : Set X := ⋃ t, ((A t).weilCycle hn).support
  have hS : S.Finite := Set.finite_iUnion (fun t => cartierAtlas_weilCycle_finite_support X hn (A t))
  let : Fintype S := hS.fintype
  let M (t : τ) (x : S) : ℚ := (A t).coefficient hn x.1
  have hm : ∀ x : S, 0 ≤ rationalCoefficientMap M c x := by
    intro x
    simpa [rationalCoefficientMap, M] using he x.1
  obtain ⟨J, hJ, w, z, hw, hzpos, _, hsum⟩ :=
    effective_integral_coefficient_decomposition M c hm
  let : Fintype J := hJ
  choose B hB using fun j => exists_cartierAtlas_integralCombination X A (z j)
  have hcoeff (j : J) (x : X) : (B j).coefficient hn x =
      ∑ t, z j t * (A t).coefficient hn x :=
    cartierAtlas_integralCombination_coefficients X hn A (z j) (B j)
      (fun x => ⟨(hB j x).1, (hB j x).2.2⟩) x
  have hzoutside (x : X) (hx : x ∉ S) (t : τ) : (A t).coefficient hn x = 0 := by
    by_contra h
    exact hx (Set.mem_iUnion.mpr ⟨t, h⟩)
  refine ⟨J, hJ, w, z, B, hw, hsum, ?_, fun j x => ⟨(hB j x).1, (hB j x).2.2⟩⟩
  intro j
  apply (cartierAtlas_effective_iff_weil_nonneg X hn (B j)).mpr
  intro x
  change 0 ≤ (B j).coefficient hn x
  rw [hcoeff]
  by_cases hx : x ∈ S
  · have hp := hzpos j ⟨x, hx⟩
    change (0 : ℝ) ≤ ∑ t, (z j t : ℝ) * ((A t).coefficient hn x : ℝ) at hp
    exact_mod_cast hp
  · simp [hzoutside x hx]

/-- Pullback commutes with integral combinations at actual source
codimension-one points, including those above a higher-codimension center.
This identity is proved from local equations and actual stalk units. -/
theorem cartierAtlas_pullback_integralCombination_coefficients {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Y) [IsDominant f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas Y ι) (z : τ → ℤ)
    (B : CartierAtlas Y Y)
    (hB : ∀ y : Y, y ∈ B.chart y ∧
      B.equation y = ∏ t, (A t).equation ((A t).covers y).choose ^ z t)
    (C : τ → CartierAtlas X X)
    (hC : ∀ t x, x ∈ (C t).chart x ∧
      (C t).equation x = Units.map (dominantFunctionFieldMap f : _ →* _)
        ((A t).equation ((A t).covers (f x)).choose))
    (B' : CartierAtlas X X)
    (hB' : ∀ x : X, x ∈ B'.chart x ∧
      B'.equation x = Units.map (dominantFunctionFieldMap f : _ →* _)
        (B.equation (B.covers (f x)).choose)) :
    ∀ x : X, B'.coefficient hnX x = ∑ t, z t * (C t).coefficient hnX x := by
  classical
  intro x
  by_cases hx : Order.coheight x = 1
  · rw [cartierAtlas_pullback_coefficient_eq hnX f B B' hB' x hx (f x) (hB (f x)).1,
      (hB (f x)).2, map_prod]
    simp_rw [map_zpow]
    have := hnX x
    have := normal_codimensionOne_stalk_isDVR X x hx
    unfold schemeRationalOrder
    rw [dvr_rationalOrder_prod]
    apply Finset.sum_congr rfl
    intro t _
    rw [dvr_rationalOrder_zpow,
      cartierAtlas_coefficient_eq X hnX (C t) x x hx (hC t x).1, (hC t x).2]
    rfl
  · simp [CartierAtlas.coefficient, hx]

/-- This finite-sum identity translates equality in the original
coefficient coordinates into equality of the actual weighted Weil cycles. -/
theorem realWeightedWeilCycle_eq_of_integral_coefficients (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι κ τ J : Type*} [Fintype τ] [Fintype J]
    (A : τ → CartierAtlas X ι) (B : J → CartierAtlas X κ)
    (c : τ → ℝ) (w : J → ℝ) (z : J → τ → ℤ)
    (hsum : (∑ j, w j • (fun t => (z j t : ℝ))) = c)
    (hcoeff : ∀ j x, (B j).coefficient hn x = ∑ t, z j t * (A t).coefficient hn x) :
    (∑ j, (B j).weightedWeilCycle hn (w j)) =
      ∑ t, (A t).weightedWeilCycle hn (c t) := by
  classical
  ext x
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  change (∑ j, w j * ((B j).coefficient hn x : ℝ)) =
    ∑ t, c t * ((A t).coefficient hn x : ℝ)
  simp_rw [hcoeff, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have hs := congrFun hsum t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [hs]

/-- Construct a genuine effective Cartier pullback and retain its full
chart data, local equations and inverse-image geometric support. -/
theorem exists_effective_cartierAtlas_pullback_data {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    {ι : Type*} (A : CartierAtlas Y ι) (hA : A.Effective) :
    ∃ B : CartierAtlas X X, B.Effective ∧
      B.vanishingSupport = f ⁻¹' A.vanishingSupport ∧
      ∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧
        z ∈ B.chart z ∧ B.equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
          (A.equation (A.covers (f z)).choose) := by
  classical
  obtain ⟨B, hB⟩ := exists_cartierAtlas_pullback f A
  have heffective : B.Effective := by
    intro z x hx
    obtain ⟨r, hr⟩ := hA _ (f x) ((hB z).1 hx)
    refine ⟨(f.stalkMap x).hom r, ?_⟩
    rw [(hB z).2.2]
    rw [← dominantFunctionFieldMap_stalk f x r, hr]
    rfl
  refine ⟨B, heffective, ?_, hB⟩
  ext x
  rw [cartierAtlas_support_eq_on_chart X B x x (hB x).2.1,
    Set.mem_preimage, cartierAtlas_support_eq_on_chart Y A _ (f x) (A.covers (f x)).choose_spec,
    (hB x).2.2]
  obtain ⟨r, hr⟩ := hA _ (f x) (A.covers (f x)).choose_spec
  exact not_congr (rationalUnitAt_regular_pullback_iff f x _ r hr)

/-- For arbitrary original real weights, the termwise pullback of an
effective real Cartier combination is effective and has exactly the
inverse-image geometric support. Compatibility with the constructed
effective decomposition is proved from the original local equations;
it is not an extra hypothesis. No separability or characteristic
restriction is imposed. This theorem does not prove fiber dichotomy. -/
theorem exists_realCartier_termwise_pullback_support {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsDominant f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas Y ι) (c : τ → ℝ)
    (he : ∀ y : Y, 0 ≤ ∑ t, c t * ((A t).coefficient hnY y : ℝ)) :
    ∃ C : τ → CartierAtlas X X,
      CycleEffective (∑ t, (C t).weightedWeilCycle hnX (c t)) ∧
      closure (∑ t, (C t).weightedWeilCycle hnX (c t)).support =
        f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnY (c t)).support ∧
      ∀ t x, (C t).chart x ≤ f ⁻¹ᵁ (A t).chart ((A t).covers (f x)).choose ∧
        x ∈ (C t).chart x ∧ (C t).equation x = Units.map (dominantFunctionFieldMap f : _ →* _)
          ((A t).equation ((A t).covers (f x)).choose) := by
  classical
  obtain ⟨J, hJ, w, z, B, hw, hsum, hB, hBeq⟩ :=
    exists_realCartier_effective_decomposition_equations Y hnY A c he
  let : Fintype J := hJ
  choose C hC using fun t => exists_cartierAtlas_pullback f (A t)
  choose B' hB' hsupp hB'eq using fun j =>
    exists_effective_cartierAtlas_pullback_data f (B j) (hB j)
  have hbase : (∑ j, (B j).weightedWeilCycle hnY (w j)) =
      ∑ t, (A t).weightedWeilCycle hnY (c t) :=
    realWeightedWeilCycle_eq_of_integral_coefficients Y hnY A B c w z hsum
      (fun j => cartierAtlas_integralCombination_coefficients Y hnY A (z j) (B j) (hBeq j))
  have hsource : (∑ j, (B' j).weightedWeilCycle hnX (w j)) =
      ∑ t, (C t).weightedWeilCycle hnX (c t) :=
    realWeightedWeilCycle_eq_of_integral_coefficients X hnX C B' c w z hsum
      (fun j => cartierAtlas_pullback_integralCombination_coefficients hnX f A (z j)
        (B j) (hBeq j) C (fun t x => (hC t x).2) (B' j) (fun x => (hB'eq j x).2))
  have heff : CycleEffective (∑ j, (B' j).weightedWeilCycle hnX (w j)) := by
    intro x
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    change 0 ≤ ∑ j, w j * ((B' j).coefficient hnX x : ℝ)
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hw j)
    exact_mod_cast effective_cartierAtlas_weil_nonneg X hnX (B' j) (hB' j) x
  have hs : closure (∑ j, (B' j).weightedWeilCycle hnX (w j)).support =
      f ⁻¹' closure (∑ j, (B j).weightedWeilCycle hnY (w j)).support := by
    rw [effective_cartier_real_sum_support X hnX B' w hw hB',
      effective_cartier_real_sum_support Y hnY B w hw hB]
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    simp_rw [hsupp, Set.mem_preimage]
  rw [hsource] at heff hs
  rw [hbase] at hs
  exact ⟨C, heff, hs, hC⟩

/-- A proper birational modification descends both fiber-support
alternatives for the actual termwise pullback of an effective R-Cartier
presentation. Actual surjectivity, effectivity and support pullback are
proved here. This is an equivalence of the two alternatives upstairs
and downstairs; it does not prove that the alternative always holds. -/
theorem exists_realCartier_termwise_fiber_descent {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (p : X ⟶ Y) [IsProper p] (hp : BirationalMorphism p)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas Y ι) (c : τ → ℝ)
    (he : ∀ y : Y, 0 ≤ ∑ t, c t * ((A t).coefficient hnY y : ℝ)) :
    letI := birationalMorphism_dominant p hp
    ∃ C : τ → CartierAtlas X X,
      CycleEffective (∑ t, (C t).weightedWeilCycle hnX (c t)) ∧
      (∀ t x, (C t).equation x = Units.map (dominantFunctionFieldMap p : _ →* _)
        ((A t).equation ((A t).covers (p x)).choose)) ∧
      ∀ (T : Type*) (g : Y → T) (y : T),
        (Disjoint {x | g (p x) = y} (closure (∑ t, (C t).weightedWeilCycle hnX (c t)).support) ∨
          {x | g (p x) = y} ⊆ closure (∑ t, (C t).weightedWeilCycle hnX (c t)).support) ↔
        (Disjoint {x | g x = y} (closure (∑ t, (A t).weightedWeilCycle hnY (c t)).support) ∨
          {x | g x = y} ⊆ closure (∑ t, (A t).weightedWeilCycle hnY (c t)).support) := by
  have := birationalMorphism_dominant p hp
  obtain ⟨C, hC, hs, heq⟩ := exists_realCartier_termwise_pullback_support hnX hnY p A c he
  have hsurj : Function.Surjective p := (proper_birational_surjective p hp).1
  refine ⟨C, hC, fun t x => (heq t x).2.2, ?_⟩
  intro T g y
  rw [hs, composite_fiber, ← disjoint_iff_preimage_disjoint p hsurj,
    ← subset_iff_preimage_subset p hsurj]

end Negativity
