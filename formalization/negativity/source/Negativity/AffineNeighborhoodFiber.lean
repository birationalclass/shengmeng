module

public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual fiber-point homeomorphism under restriction to a base open.
Its underlying map forgets membership in that open, and its inverse
recovers membership from the actual fiber equation. -/
def actualRestrictedFiberPointsHomeomorph {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    ((f ∣_ U) ⁻¹' {⟨y, hy⟩}) ≃ₜ (f ⁻¹' {y}) where
  toFun x := ⟨x.1.1, by
    have h := congrArg Subtype.val (Set.mem_singleton_iff.mp x.2)
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, morphismRestrict_base_coe] using h⟩
  invFun x := ⟨⟨x.1, by
    change f x.1 ∈ U
    rw [Set.mem_singleton_iff.mp x.2]
    exact hy⟩, by
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using Set.mem_singleton_iff.mp x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def actualRestrictedFiberHomeomorph {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    (f ∣_ U).fiber ⟨y, hy⟩ ≃ₜ f.fiber y :=
  ((f ∣_ U).fiberHomeo ⟨y, hy⟩).trans
    ((actualRestrictedFiberPointsHomeomorph f U y hy).trans (f.fiberHomeo y).symm)

/-- Final theorem: actual scheme-theoretic fiber connectedness can be
checked after restricting to any actual base-open neighborhood of the
point. The actual homeomorphism is constructed; no fiber comparison is
given as an input. Affine neighborhoods are a special case. -/
theorem actual_restricted_fiber_connected_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    ConnectedSpace ((f ∣_ U).fiber ⟨y, hy⟩) ↔ ConnectedSpace (f.fiber y) :=
  (actualRestrictedFiberHomeomorph f U y hy).connectedSpace_iff

end
end Negativity
