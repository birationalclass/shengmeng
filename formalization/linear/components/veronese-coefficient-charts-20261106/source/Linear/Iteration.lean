module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Set.Function

/-! # Total invariance under iteration
These statements are actual set/function results. Polynomial degree and
geometric fiber degree are addressed separately, not assumed to follow from
set-theoretic invariance.
-/

@[expose] public section
namespace LinearStudy
variable {X : Type*} (f : X → X) (V : Set X)

theorem total_invariance_membership (h : f ⁻¹' V = V) (x : X) :
    f x ∈ V ↔ x ∈ V := by
  change x ∈ f ⁻¹' V ↔ x ∈ V
  rw [h]

theorem total_invariance_iterate (h : f ⁻¹' V = V) (k : ℕ) :
    (f^[k]) ⁻¹' V = V := by
  ext x
  induction k with
  | zero => simp
  | succ k ih =>
    change f^[k + 1] x ∈ V ↔ x ∈ V
    rw [Function.iterate_succ_apply', total_invariance_membership f V h]
    exact ih

theorem invariant_restriction (h : f ⁻¹' V = V) (x : V) : f x ∈ V :=
  (total_invariance_membership f V h x).mpr x.property

def restrictInvariant (h : f ⁻¹' V = V) : V → V :=
  fun x => ⟨f x, invariant_restriction f V h x⟩

theorem invariant_restriction_surjective (hf : Function.Surjective f)
    (h : f ⁻¹' V = V) : Function.Surjective (restrictInvariant f V h) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hv : x ∈ V := (total_invariance_membership f V h x).mp (hx ▸ y.property)
  exact ⟨⟨x, hv⟩, Subtype.ext hx⟩

end LinearStudy
