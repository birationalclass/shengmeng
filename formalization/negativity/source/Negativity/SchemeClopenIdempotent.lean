module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A genuine nontrivial clopen decomposition of an actual scheme
constructs a nontrivial idempotent in its actual global section ring.
The product comparison is proved from the genuine structure-sheaf
gluing property, not supplied as an algebraic hypothesis. -/
theorem actual_clopen_nontrivial_global_idempotent (X : Scheme.{u})
    (S : Set X) (hS : IsClopen S) (h0 : S ≠ ∅) (h1 : S ≠ Set.univ) :
    ∃ a : Γ(X, ⊤), a * a = a ∧ a ≠ 0 ∧ a ≠ 1 := by
  classical
  let U : X.Opens := ⟨S, hS.isOpen⟩
  let V : X.Opens := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  have : Nonempty U := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h0
    exact ⟨⟨x, hx⟩⟩
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr
      (show Sᶜ ≠ ∅ from fun h => h1 (Set.compl_empty_iff.mp h))
    exact ⟨⟨x, hx⟩⟩
  have hdisj : U ⊓ V = ⊥ := by
    ext x
    change (x ∈ S ∧ x ∈ Sᶜ) ↔ False
    simp
  have hcover : U ⊔ V = ⊤ := by
    ext x
    change (x ∈ S ∨ x ∈ Sᶜ) ↔ True
    exact iff_true_intro (em (x ∈ S))
  let ee : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hdisj).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have ee' : Γ(X, ⊤) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) := by
    rw [← hcover]
    exact ee
  let e := ee'.commRingCatIsoToRingEquiv
  let a := e.symm (1, 0)
  refine ⟨a, ?_, ?_, ?_⟩
  · apply e.injective
    simp [a]
  · intro ha
    have h := congrArg (fun r => (e r).1) ha
    simp [a] at h
  · intro ha
    have h := congrArg (fun r => (e r).2) ha
    simp [a] at h

/-- Final theorem: an actual nonempty scheme is connected if its actual
global ring has only the two trivial idempotents. The missing formal-
functions step for proper fibers must still establish this condition
for the actual fiber ring; this theorem does not assume that geometry
has already been proved. -/
theorem actual_scheme_connected_of_global_idempotents_trivial
    (X : Scheme.{u}) [Nonempty X]
    (h : ∀ a : Γ(X, ⊤), a * a = a → a = 0 ∨ a = 1) :
    ConnectedSpace X := by
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  by_contra hn
  have hn := not_or.mp hn
  obtain ⟨a, ha, hzero, hone⟩ :=
    actual_clopen_nontrivial_global_idempotent X S hS hn.1 hn.2
  exact (h a ha).elim hzero hone

end
end Negativity
