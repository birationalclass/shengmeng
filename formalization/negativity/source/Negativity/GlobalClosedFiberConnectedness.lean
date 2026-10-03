module

public import Negativity.RelativeFormalConnectedness
public import Negativity.AffineNeighborhoodFiber
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The precise remaining geometric comparison: on every actual affine
base neighborhood and at every actual closed point, the constructed
relative formal-functions map is bijective. Its source may be nonaffine. -/
def ActualClosedFiberFormalFunctions {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : Y.affineOpens) (v : U.1), IsClosed ({v} : Set U.1) →
    letI : IsAffine U.1 := U.2
    Function.Bijective
      (actualRelativeFormalFunctionsMap (f ∣_ U.1) (actualClosedPointIdeal U.1 v))

/-- Final theorem, explicitly conditional: actual closed-point fibers
over an arbitrary locally Noetherian base are connected if the precise
constructed affine-neighborhood formal-functions comparisons are
bijective. Actual neighborhood selection, fiber homeomorphism, relative
idempotent construction and completed-ring contradiction are all proved.
The formal-functions hypothesis remains explicit and unproved here. -/
theorem actual_closed_fibers_connected_of_affine_formal_functions
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Surjective f] (hff : ActualClosedFiberFormalFunctions f) :
    ∀ y : Y, IsClosed ({y} : Set Y) → ConnectedSpace (f.fiber y) := by
  intro y hy
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := y) trivial
  let V : Y.affineOpens := ⟨U, hU⟩
  let v : U := ⟨y, hyU⟩
  have : IsAffine U := hU
  have hv : IsClosed ({v} : Set U) := by
    have hset : (Subtype.val : U → Y) ⁻¹' {y} = {v} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
      rfl
    rw [← hset]
    exact hy.preimage continuous_subtype_val
  have : Surjective (f ∣_ U) := ⟨by
    intro z
    obtain ⟨x, hx⟩ := f.surjective z.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change f x ∈ U
      rw [hx]
      exact z.2
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx⟩
  have hc := actual_closed_fiber_connected_of_relative_formal_functions
    (f ∣_ U) v hv (hff V v hv)
  exact (actual_restricted_fiber_connected_iff f U y hyU).mp hc

end
end Negativity
