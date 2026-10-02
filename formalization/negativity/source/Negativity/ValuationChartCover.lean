module

public import Negativity.FunctionFieldDegree
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (priority := low) (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] : Algebra k[X] L :=
  ((algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))).toAlgebra
local instance (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L] :
    IsScalarTower k[X] (RatFunc k) L := IsScalarTower.of_algebraMap_eq' rfl
local instance (priority := low) (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] : Algebra (RationalInfinityRing k) L :=
  ((algebraMap (RatFunc k) L).comp
    (algebraMap (RationalInfinityRing k) (RatFunc k))).toAlgebra
local instance (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L] :
    IsScalarTower (RationalInfinityRing k) (RatFunc k) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A valuation subring containing all constants has trivial valuation
on the actual ground field: a nonzero constant and its inverse are units. -/
theorem valuation_constants_trivial (k L : Type*) [Field k] [Field L]
    [Algebra k L] (A : ValuationSubring L)
    (hk : ∀ c : k, algebraMap k L c ∈ A) : A.valuation.IsTrivialOn k where
  eq_one c hc := by
    have hcL : algebraMap k L c ≠ 0 := by
      simpa only [map_zero] using (algebraMap k L).injective.ne hc
    have hci : (algebraMap k L c)⁻¹ ∈ A := by
      simpa only [map_inv₀] using hk c⁻¹
    have hu : IsUnit (⟨algebraMap k L c, hk c⟩ : A) :=
      IsUnit.of_mul_eq_one ⟨(algebraMap k L c)⁻¹, hci⟩ (by
        ext
        exact mul_inv_cancel₀ hcL)
    exact (A.valuation_eq_one_iff _).mp hu

/-- Every integral element over a ring lying in a valuation ring also
lies in that valuation ring. This uses genuine integral closedness of
valuation rings and the actual fraction-field inclusion. -/
theorem integral_element_mem_valuation
    (R L : Type*) [CommRing R] [Field L] [Algebra R L]
    (A : ValuationSubring L) (hR : ∀ r : R, algebraMap R L r ∈ A)
    (x : L) (hx : IsIntegral R x) : x ∈ A := by
  let : Algebra R A := ((algebraMap R L).codRestrict A.toSubring hR).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) hx.tower_top
  exact ha ▸ a.2

/-- A ground-field valuation at which the rational parameter has a pole
contains the actual infinity DVR of k(t). This follows from the polynomial
degree formula for an arbitrary valuation trivial on constants. -/
theorem rational_infinity_ring_mem_of_parameter_pole
    (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L]
    [Algebra k L] [IsScalarTower k (RatFunc k) L]
    (A : ValuationSubring L) (hk : ∀ c : k, algebraMap k L c ∈ A)
    (ht : algebraMap (RatFunc k) L RatFunc.X ∉ A)
    (r : RationalInfinityRing k) : algebraMap (RatFunc k) L (r : RatFunc k) ∈ A := by
  classical
  let w := A.valuation.comap (algebraMap (RatFunc k) L)
  have : A.valuation.IsTrivialOn k := valuation_constants_trivial k L A hk
  have : w.IsTrivialOn k := ⟨fun c hc ↦ by
    change A.valuation ((algebraMap (RatFunc k) L) (algebraMap k (RatFunc k) c)) = 1
    rw [← IsScalarTower.algebraMap_apply k (RatFunc k) L]
    exact Valuation.IsTrivialOn.eq_one c hc⟩
  have htval : 1 < w RatFunc.X := by
    change 1 < A.valuation (algebraMap (RatFunc k) L RatFunc.X)
    exact lt_of_not_ge (by simpa only [A.valuation_le_one_iff] using ht)
  rw [← A.valuation_le_one_iff]
  change w (r : RatFunc k) ≤ 1
  by_cases hr : (r : RatFunc k) = 0
  · simp [hr]
  have hdeg : (r : RatFunc k).intDegree ≤ 0 := by
    apply WithZero.exp_le_exp.mp
    have hrval : RatFunc.inftyValuation k (r : RatFunc k) ≤ 1 := r.2
    simpa only [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero k hr,
      WithZero.exp_zero] using hrval
  have hnd : (r : RatFunc k).num.natDegree ≤ (r : RatFunc k).denom.natDegree := by
    dsimp [RatFunc.intDegree] at hdeg
    omega
  have hp := RatFunc.num_ne_zero hr
  have hq := RatFunc.denom_ne_zero (r : RatFunc k)
  rw [← RatFunc.num_div_denom (r : RatFunc k), map_div₀]
  change w (((r : RatFunc k).num : RatFunc k)) /
    w (((r : RatFunc k).denom : RatFunc k)) ≤ 1
  rw [
    Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X k htval hp,
    Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X k htval hq]
  exact (div_le_one₀ (pow_pos (lt_trans zero_lt_one htval) _)).mpr
    (pow_le_pow_right' htval.le hnd)

/-- Final theorem: every actual ground-field valuation ring of L lies
over the finite parameter chart or over the infinity DVR chart. Each
chart's actual integral closure in L is contained in that valuation ring.
There is no assumed place-cover or prime-classification input. -/
theorem functionField_valuation_integralClosure_chart_cover
    (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L]
    [Algebra k L] [IsScalarTower k (RatFunc k) L]
    (A : ValuationSubring L) (hk : ∀ c : k, algebraMap k L c ∈ A) :
    (∀ r : FunctionFieldPlaces.FiniteRing k L, (r : L) ∈ A) ∨
      (∀ r : FunctionFieldPlaces.InfinityRing k L, (r : L) ∈ A) := by
  classical
  by_cases ht : algebraMap (RatFunc k) L RatFunc.X ∈ A
  · left
    have hpoly : ∀ p : k[X], algebraMap k[X] L p ∈ A := by
      let w := A.valuation.comap (algebraMap (RatFunc k) L)
      have : A.valuation.IsTrivialOn k := valuation_constants_trivial k L A hk
      have : w.IsTrivialOn k := ⟨fun c hc ↦ by
        change A.valuation ((algebraMap (RatFunc k) L) (algebraMap k (RatFunc k) c)) = 1
        rw [← IsScalarTower.algebraMap_apply k (RatFunc k) L]
        exact Valuation.IsTrivialOn.eq_one c hc⟩
      intro p
      rw [← A.valuation_le_one_iff]
      change w (algebraMap k[X] (RatFunc k) p) ≤ 1
      exact Polynomial.valuation_le_one_of_valuation_X_le_one k
        (by change A.valuation (algebraMap (RatFunc k) L RatFunc.X) ≤ 1
            exact (A.valuation_le_one_iff _).mpr ht) p
    intro r
    exact integral_element_mem_valuation k[X] L A hpoly (r : L) r.2
  · right
    have hinf : ∀ r : RationalInfinityRing k,
        algebraMap (RationalInfinityRing k) L r ∈ A :=
      rational_infinity_ring_mem_of_parameter_pole k L A hk ht
    intro r
    exact integral_element_mem_valuation (RationalInfinityRing k) L A hinf (r : L) r.2

end
end Negativity
