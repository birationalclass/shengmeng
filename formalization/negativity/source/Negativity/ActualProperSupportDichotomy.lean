module

public import Negativity.ActualConnectedSupport
public import Negativity.ClosedFiberSupportDetection
public import Negativity.ClosedFiberCompleteness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem, explicitly conditional: actual proper real-Cartier
support negativity (2) on every fiber follows from connectedness of the
actual closed-point fibers. Completeness, crossing curves, actual
intersection signs and passage from closed to all base points are proved
internally. Closed-fiber connectedness is the remaining geometric input. -/
theorem actual_proper_support_dichotomy_of_connected_closed_fibers
    {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -r t))
    (hconn : ∀ y : Y, IsClosed ({y} : Set Y) → ConnectedSpace (f.fiber y)) :
    ∀ y : Y,
      (∀ x : X, f x = y →
        x ∉ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) ∨
      (∀ x : X, f x = y →
        x ∈ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) := by
  classical
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace b
  apply actual_fiber_closed_subset_dichotomy_of_closed_points f _ isClosed_closure
  intro y hy
  have := hconn y hy
  have := actual_closed_fiber_proper_over_ground_field k b f y hy
  have hcontract : ∀ z w : f.fiber y, f (f.fiberι y z) = f (f.fiberι y w) := by
    intro z w
    have hz : f (f.fiberι y z) = y := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.fiberHomeo_apply]
        using (f.fiberHomeo y z).property
    have hw : f (f.fiberι y w) = y := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.fiberHomeo_apply]
        using (f.fiberHomeo y w).property
    exact hz.trans hw.symm
  rcases actual_connected_contracted_scheme_support_dichotomy hnX k b f A r he hnef
    (f.fiber y) (f.fiberι y) hcontract with hn | ha
  · left
    intro x hx
    let z := (f.fiberHomeo y).symm ⟨x, by simpa using hx⟩
    have hz := hn z
    simpa only [z, Scheme.Hom.fiberι_fiberHomeo_symm] using hz
  · right
    intro x hx
    let z := (f.fiberHomeo y).symm ⟨x, by simpa using hx⟩
    have hz := ha z
    simpa only [z, Scheme.Hom.fiberι_fiberHomeo_symm] using hz

end
end Negativity
