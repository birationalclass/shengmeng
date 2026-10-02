module

public import Negativity.CurveChartPlaces
public import Negativity.DvrAdicOrders
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A chart-prime valuation equal to an actual curve-point valuation has
the actual local order at that point. No order-identification input is used. -/
theorem dedekind_prime_actual_curve_order
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R C.functionField] [IsFractionRing R C.functionField]
    (p : HeightOneSpectrum R) (x : C) (hx : Order.coheight x = 1)
    (hp : normalCurvePointValuation C hn x hx = (p.valuation C.functionField).valuationSubring)
    (a : C.functionFieldˣ) :
    heightOneOrder C.functionField p a = schemeRationalOrder C hn x hx a := by
  have hlift := normalCurvePointValuation_lift C hn x hx
  rw [hp] at hlift
  obtain ⟨l, hl, hcx⟩ := hlift
  have hxl : Order.coheight (l (IsLocalRing.closedPoint
      (p.valuation C.functionField).valuationSubring)) = 1 := hcx.symm ▸ hx
  rw [dedekind_prime_order_eq_valuationRing_order]
  simpa only [hcx] using normal_curve_valuation_center_order C hn
    (p.valuation C.functionField).valuationSubring l hl hxl a

variable (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    [Algebra (RatFunc k) C.functionField] [Algebra k C.functionField]
    [IsScalarTower k (RatFunc k) C.functionField]
    [FiniteDimensional (RatFunc k) C.functionField]
    [Algebra.IsSeparable (RatFunc k) C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b)

/-- The actual principal orders on both constructed normalization charts. -/
def twoChartPrincipalDivisor (a : C.functionFieldˣ) :
    FunctionFieldPlaces.TwoChartPlace k C.functionField →₀ ℤ :=
  (affinePrincipalDivisor C.functionField a :
    HeightOneSpectrum (FunctionFieldPlaces.FiniteRing k C.functionField) →₀ ℤ).sumElim
      (affinePrincipalDivisor C.functionField a :
        HeightOneSpectrum (FunctionFieldPlaces.InfinityRing k C.functionField) →₀ ℤ)

include hd b hbase

theorem twoChartPrincipalDivisor_actual_order
    (a : C.functionFieldˣ) (p : FunctionFieldPlaces.TwoChartPlace k C.functionField) :
    twoChartPrincipalDivisor C k a p =
      schemeRationalOrder C hn (curveTwoChartCenter C hn hd k b hbase p)
        (curveTwoChartCenter C hn hd k b hbase p).2 a := by
  cases p with
  | inl p =>
    exact dedekind_prime_actual_curve_order C hn _ p _ _
      (curveTwoChartCenter_valuation C hn hd k b hbase (.inl p)) a
  | inr q =>
    exact dedekind_prime_actual_curve_order C hn _ q _ _
      (curveTwoChartCenter_valuation C hn hd k b hbase (.inr q)) a

/-- The principal divisor on the actual complete curve. Its coefficients
are proved below to be the actual stalk orders at every closed point. -/
def curvePrincipalDivisor (a : C.functionFieldˣ) :
    {x : C // Order.coheight x = 1} →₀ ℤ :=
  (twoChartPrincipalDivisor C k a).mapDomain (curveTwoChartCenter C hn hd k b hbase)

theorem curvePrincipalDivisor_coefficient (a : C.functionFieldˣ)
    (x : {x : C // Order.coheight x = 1}) :
    curvePrincipalDivisor C hn hd k b hbase a x = schemeRationalOrder C hn x x.2 a := by
  obtain ⟨p, rfl⟩ := (proper_normal_curve_twoChart_centers_bijective C hn hd k b hbase).2 x
  rw [curvePrincipalDivisor, Finsupp.mapDomain_apply_of_injective
    (proper_normal_curve_twoChart_centers_bijective C hn hd k b hbase).1]
  exact twoChartPrincipalDivisor_actual_order C hn hd k b hbase a p

/-- Final theorem: the principal divisor on an actual proper normal curve
over an algebraically closed field has finite support, has the actual local
DVR orders as coefficients at every closed point, and has degree zero.
The compatible finite separable parameter is explicit in the hypotheses;
there is no assumed place list, center correspondence, local-order equality,
or degree-zero premise. Arbitrary characteristic is allowed. -/
theorem proper_normal_curve_principal_degree_zero [IsAlgClosed k]
    (a : C.functionFieldˣ) :
    (∀ x : {x : C // Order.coheight x = 1},
      curvePrincipalDivisor C hn hd k b hbase a x = schemeRationalOrder C hn x x.2 a) ∧
    (curvePrincipalDivisor C hn hd k b hbase a).degree = 0 := by
  refine ⟨curvePrincipalDivisor_coefficient C hn hd k b hbase a, ?_⟩
  rw [curvePrincipalDivisor, Finsupp.degree_mapDomain, twoChartPrincipalDivisor,
    Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]
  exact functionField_principal_order_sum_zero k C.functionField a

end
end Negativity
