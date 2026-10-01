module

public import Negativity.FractionFieldOrders
public import Negativity.CodimensionSupport
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Local rational equations on an affine cover, with regular unit transitions
in the actual scheme stalks. These are Cartier presentation data, not an
assumed Weil divisor or an assumed finiteness of its coefficients. -/
structure CartierAtlas (X : Scheme) [IsIntegral X] (ι : Type*) where
  chart : ι → X.Opens
  affine : ∀ i, IsAffineOpen (chart i)
  nonempty : ∀ i, Nonempty (chart i)
  covers : ∀ x : X, ∃ i, x ∈ chart i
  equation : ι → X.functionFieldˣ
  transition : ∀ i j (x : X), x ∈ chart i → x ∈ chart j →
    ∃ u : (X.presheaf.stalk x)ˣ,
      Units.map (algebraMap (X.presheaf.stalk x) X.functionField : _ →* _) u *
        equation i = equation j

noncomputable def schemeRationalOrder (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (x : X) (hx : Order.coheight x = 1) (a : X.functionFieldˣ) : ℤ := by
  have := hn x
  have := normal_codimensionOne_stalk_isDVR X x hx
  exact DvrRationalOrder (X.presheaf.stalk x) X.functionField a

/-- Actual Cartier unit transitions glue the codimension-one coefficients. -/
theorem cartierAtlas_order_agrees (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) {ι : Type*}
    (A : CartierAtlas X ι) (i j : ι) (x : X) (hx : Order.coheight x = 1)
    (hi : x ∈ A.chart i) (hj : x ∈ A.chart j) :
    schemeRationalOrder X hn x hx (A.equation i) =
      schemeRationalOrder X hn x hx (A.equation j) := by
  obtain ⟨u, hu⟩ := A.transition i j x hi hj
  have := hn x
  have := normal_codimensionOne_stalk_isDVR X x hx
  unfold schemeRationalOrder
  rw [← hu, dvr_rationalOrder_unit_transition]

/-- The local equation of a rational function has zero coefficient when its
numerator and denominator are both regular units at the point. -/
theorem schemeRationalOrder_zero_of_unit_germs (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (a : X.functionFieldˣ) (r s : Γ(X, U))
    (h : (a : X.functionField) * X.germToFunctionField U s = X.germToFunctionField U r)
    (x : X) (hxU : x ∈ U) (hx : Order.coheight x = 1)
    (hr : IsUnit (X.presheaf.germ U x hxU r))
    (hs : IsUnit (X.presheaf.germ U x hxU s)) :
    schemeRationalOrder X hn x hx a = 0 := by
  have := hn x
  have := normal_codimensionOne_stalk_isDVR X x hx
  unfold schemeRationalOrder
  rw [dvr_rationalOrder_represents _ _ a _ _ hr.ne_zero hs.ne_zero (by
    simpa only [Scheme.algebraMap_germ_eq_germToFunctionField] using h)]
  simp [LocalFractionOrder, addVal_eq_zero_iff.mpr hr, addVal_eq_zero_iff.mpr hs]

/-- Finite codimension-one support of an actual rational equation on an
affine chart, in arbitrary dimension. Numerator and denominator are chosen
from the actual chart ring using its fraction-field property. -/
theorem finite_schemeRationalOrder_on_affine (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (a : X.functionFieldˣ) :
    {x : U | ∃ hx : Order.coheight (x : X) = 1,
      schemeRationalOrder X hn x hx a ≠ 0}.Finite := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) (a : X.functionField)
  have hs : (s : Γ(X, U)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    intro hz
    have hsk : algebraMap Γ(X, U) X.functionField (s : Γ(X, U)) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective Γ(X, U) X.functionField).ne hs
    exact mul_ne_zero a.ne_zero hsk (by simpa only [hz, map_zero] using h)
  apply ((finite_codimensionOne_nonunit_germs X U hU r hr).union
    (finite_codimensionOne_nonunit_germs X U hU s hs)).subset
  rintro x ⟨hx, ha⟩
  by_cases hru : IsUnit (X.presheaf.germ U x x.2 r)
  · right
    refine ⟨hx, ?_⟩
    intro hsu
    exact ha (schemeRationalOrder_zero_of_unit_germs X hn U a r s h x x.2 hx hru hsu)
  · exact Or.inl ⟨hx, hru⟩

noncomputable def CartierAtlas.coefficient {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] {ι : Type*} (A : CartierAtlas X ι)
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : X) : ℤ := by
  classical
  exact if hx : Order.coheight x = 1 then
    schemeRationalOrder X hn x hx (A.equation (A.covers x).choose) else 0

/-- The glued coefficient is computed using any chart containing the point. -/
theorem cartierAtlas_coefficient_eq (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) {ι : Type*}
    (A : CartierAtlas X ι) (i : ι) (x : X) (hx : Order.coheight x = 1)
    (hi : x ∈ A.chart i) : A.coefficient hn x = schemeRationalOrder X hn x hx (A.equation i) := by
  classical
  simp only [CartierAtlas.coefficient, dite_eq_left hx]
  exact cartierAtlas_order_agrees X hn A _ i x hx (A.covers x).choose_spec hi

/-- No global finite cover is assumed: on each affine chart the support is
finite, so the actual glued coefficient function has locally finite support. -/
theorem cartierAtlas_locallyFiniteSupport (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) : LocallyFiniteSupport (A.coefficient hn) := by
  classical
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  have : Nonempty (A.chart i) := A.nonempty i
  refine ⟨A.chart i, (A.chart i).isOpen.mem_nhds hi, ?_⟩
  apply ((finite_schemeRationalOrder_on_affine X hn (A.chart i) (A.affine i)
    (A.equation i)).image Subtype.val).subset
  rintro y ⟨hy, hcoeff⟩
  have hcy : A.coefficient hn y ≠ 0 := hcoeff
  have hc : Order.coheight y = 1 := by
    by_contra h
    exact hcy (by simp [CartierAtlas.coefficient, h])
  refine ⟨⟨y, hy⟩, ⟨hc, ?_⟩, rfl⟩
  rwa [← cartierAtlas_coefficient_eq X hn A i y hc hy]

/-- Construct the actual mathlib cycle from Cartier local equations. -/
noncomputable def CartierAtlas.weilCycle {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] {ι : Type*} (A : CartierAtlas X ι)
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : AlgebraicCycle X ℤ where
  toFun := A.coefficient hn
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦ cartierAtlas_locallyFiniteSupport X hn A x

/-- The constructed cycle is a Weil divisor; its support is in codimension one. -/
theorem cartierAtlas_weilCycle_isWeilDivisor (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) : AlgebraicCycle.IsWeilDivisor (A.weilCycle hn) := by
  classical
  intro x hx
  change Order.coheight x = 1
  by_contra h
  exact hx (by simp [CartierAtlas.weilCycle, CartierAtlas.coefficient, h])

/-- Equivalent Cartier presentations on different covers give the same
actual Weil divisor. This includes changing equations by units and refining
the affine cover; the equality is not supplied as a hypothesis. -/
theorem cartierAtlas_weilCycle_eq_of_unit_transitions (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι κ : Type*} (A : CartierAtlas X ι) (B : CartierAtlas X κ)
    (h : ∀ i j (x : X), x ∈ A.chart i → x ∈ B.chart j →
      ∃ u : (X.presheaf.stalk x)ˣ,
        Units.map (algebraMap (X.presheaf.stalk x) X.functionField : _ →* _) u *
          A.equation i = B.equation j) :
    A.weilCycle hn = B.weilCycle hn := by
  classical
  ext x
  change A.coefficient hn x = B.coefficient hn x
  by_cases hx : Order.coheight x = 1
  · obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    rw [cartierAtlas_coefficient_eq X hn A i x hx hi,
      cartierAtlas_coefficient_eq X hn B j x hx hj]
    obtain ⟨u, hu⟩ := h i j x hi hj
    have := hn x
    have := normal_codimensionOne_stalk_isDVR X x hx
    unfold schemeRationalOrder
    rw [← hu, dvr_rationalOrder_unit_transition]
  · simp [CartierAtlas.coefficient, hx]

/-- On a quasi-compact scheme the constructed divisor has finite global
support, derived from local finiteness rather than assumed as data. -/
theorem cartierAtlas_weilCycle_finite_support (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) : (A.weilCycle hn).support.Finite :=
  (A.weilCycle hn).finite_support

end Negativity
