module

public import Negativity.Coefficients
import Mathlib.Tactic

public section
namespace Negativity

/-- Negativity at the coefficient/intersection interface. The strict-transform
map, anti-ample divisor and curve/intersection properties are geometric inputs.
`avoids c B` means the curve is not contained in the support of B. -/
theorem effective_iff_push_effective {I J V C : Type*}
    [AddCommGroup V] [Module ℝ V]
    (strict : J → I) (hinj : Function.Injective strict)
    (coeff : V →ₗ[ℝ] (I →₀ ℝ)) (intersection : C → V →ₗ[ℝ] ℝ)
    (avoids : C → V → Prop) (D E : V)
    (hE : Effective (coeff E))
    (hcover : ∀ i, ExceptionalIndex strict i → 0 < coeff E i)
    (hnef : ∀ c, intersection c D ≤ 0)
    (hanti : ∀ c, intersection c E < 0)
    (hcurve : ∀ B i, ExceptionalIndex strict i → coeff B i = 0 →
      ∃ c, avoids c B)
    (hinter : ∀ B c, Effective (coeff B) → avoids c B → 0 ≤ intersection c B) :
    Effective (coeff D) ↔ Effective (birationalPush strict hinj (coeff D)) := by
  constructor
  · exact effective_push strict hinj
  · intro hpush
    have hex : ∀ i, coeff D i < 0 → ExceptionalIndex strict i :=
      fun _ hi => negative_is_exceptional strict hinj hpush hi
    apply effective_of_curve_tests coeff intersection D E hE
      (fun i hi => hcover i (hex i hi)) hnef hanti
    intro B i hB hi hzero
    obtain ⟨c, hc⟩ := hcurve B i (hex i hi) hzero
    exact ⟨c, hinter B c hB hc⟩

/-- Support containment from coverage by negative-degree curves and
nonnegative intersection off the support. These inputs remain hypotheses. -/
theorem exceptional_subset_support {X C : Type*}
    (exc supp : Set X) (curve : C → Set X) (degree : C → ℝ)
    (hcover : ∀ x ∈ exc, ∃ c, x ∈ curve c)
    (hanti : ∀ c, degree c < 0)
    (hnonneg : ∀ c, ¬ curve c ⊆ supp → 0 ≤ degree c) :
    exc ⊆ supp := by
  intro x hx
  obtain ⟨c, hc⟩ := hcover x hx
  have hsub : curve c ⊆ supp := by
    by_contra h
    exact (not_lt_of_ge (hnonneg c h)) (hanti c)
  exact hsub hc

/-- Fiber-support dichotomy conditional on the curve-existence and strict
positivity inputs. Mere topological connectedness is not used as a substitute
for the geometric existence of a curve. -/
theorem fiber_support_dichotomy {X C : Type*}
    (fiber supp : Set X) (curve : C → Set X) (degree : C → ℝ)
    (hcurve : (fiber ∩ supp).Nonempty → ¬ fiber ⊆ supp →
      ∃ c, curve c ⊆ fiber ∧ (curve c ∩ supp).Nonempty ∧ ¬ curve c ⊆ supp)
    (hpositive : ∀ c, (curve c ∩ supp).Nonempty → ¬ curve c ⊆ supp → 0 < degree c)
    (hnef : ∀ c, curve c ⊆ fiber → degree c ≤ 0) :
    Disjoint fiber supp ∨ fiber ⊆ supp := by
  by_cases hmeet : (fiber ∩ supp).Nonempty
  · right
    by_contra hsub
    obtain ⟨c, hcf, hcmeet, hcs⟩ := hcurve hmeet hsub
    exact (not_lt_of_ge (hnef c hcf)) (hpositive c hcmeet hcs)
  · left
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)

end Negativity
