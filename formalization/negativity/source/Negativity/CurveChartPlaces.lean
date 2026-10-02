module

public import Negativity.FunctionFieldValuationPlaces
public import Negativity.ValuationOrderTransport
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    [Algebra (RatFunc k) C.functionField] [Algebra k C.functionField]
    [IsScalarTower k (RatFunc k) C.functionField]
    [FiniteDimensional (RatFunc k) C.functionField]
    [Algebra.IsSeparable (RatFunc k) C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b)

include hd b hbase

/-- Each prime in the constructed charts has an actual closed center on C.
The point and its DVR valuation are obtained from the proper Scheme map. -/
theorem curve_twoChart_center_exists
    (p : FunctionFieldPlaces.TwoChartPlace k C.functionField) :
    ∃ x : {x : C // Order.coheight x = 1},
      normalCurvePointValuation C hn x x.2 =
        FunctionFieldPlaces.twoChartValuation k C.functionField p := by
  have hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈
      FunctionFieldPlaces.twoChartValuation k C.functionField p := by
    intro c
    rw [← hbase]
    exact twoChartValuation_contains_constants k C.functionField p c
  obtain ⟨x, hx, _, he⟩ := proper_normal_curve_valuation_has_closed_point C hn hd k b
    (FunctionFieldPlaces.twoChartValuation k C.functionField p)
    (twoChartValuation_ne_top k C.functionField p) hk
  exact ⟨⟨x, hx⟩, he⟩

/-- The actual center point of a chart prime; no point lookup table is supplied. -/
def curveTwoChartCenter (p : FunctionFieldPlaces.TwoChartPlace k C.functionField) :
    {x : C // Order.coheight x = 1} :=
  Classical.choose (curve_twoChart_center_exists C hn hd k b hbase p)

theorem curveTwoChartCenter_valuation
    (p : FunctionFieldPlaces.TwoChartPlace k C.functionField) :
    normalCurvePointValuation C hn (curveTwoChartCenter C hn hd k b hbase p)
      (curveTwoChartCenter C hn hd k b hbase p).2 =
      FunctionFieldPlaces.twoChartValuation k C.functionField p :=
  Classical.choose_spec (curve_twoChart_center_exists C hn hd k b hbase p)

/-- Final theorem: actual closed points of a proper normal curve correspond
bijectively to the finite and infinity normalization primes of a compatible
finite separable parameter. Completeness, uniqueness, and chart disjointness
are proved. Existence of such a separating parameter is a separate theorem;
the place/point bijection itself is not an input. -/
theorem proper_normal_curve_twoChart_centers_bijective :
    Function.Bijective (curveTwoChartCenter C hn hd k b hbase) := by
  refine ⟨?_, ?_⟩
  · intro p q he
    apply twoChartValuation_injective k C.functionField
    rw [← curveTwoChartCenter_valuation C hn hd k b hbase p,
      ← curveTwoChartCenter_valuation C hn hd k b hbase q, he]
  · intro x
    have hk : ∀ c : k, algebraMap k C.functionField c ∈
        normalCurvePointValuation C hn x x.2 := by
      intro c
      rw [hbase]
      exact normalCurvePointValuation_contains_constants C hn x x.2 k b c
    obtain ⟨p, hp, _⟩ := functionField_valuation_unique_twoChart_place k C.functionField
      (normalCurvePointValuation C hn x x.2)
      (normalCurvePointValuation_ne_top C hn x x.2) hk
    refine ⟨p, Subtype.ext ?_⟩
    apply normalCurvePointValuation_injective C hn k b
      (curveTwoChartCenter C hn hd k b hbase p) x
      (curveTwoChartCenter C hn hd k b hbase p).2 x.2
    exact (curveTwoChartCenter_valuation C hn hd k b hbase p).trans hp

end
end Negativity
