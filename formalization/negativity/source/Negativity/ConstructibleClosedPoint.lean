module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open TopologicalSpace Topology
noncomputable section

/-- Final theorem: a nonempty constructible subset of an actual
Noetherian Jacobson topological space contains an actual closed point.
The proof reduces constructible sets to finite unions of locally closed
sets and uses the genuine Jacobson-space closed-point density theorem. -/
theorem noetherian_constructible_contains_closed_point
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [JacobsonSpace T]
    (S : Set T) (hS : IsConstructible S) (hne : S.Nonempty) :
    ∃ y ∈ S, IsClosed ({y} : Set T) := by
  classical
  have hb : IsTopologicalBasis (Set.range (fun U : Opens T => (U : Set T))) := by
    have he : Set.range (fun U : Opens T => (U : Set T)) = {U | IsOpen U} := by
      ext U
      constructor
      · rintro ⟨V, rfl⟩; exact V.isOpen
      · intro hU; exact ⟨⟨U, hU⟩, rfl⟩
    rw [he]
    exact isTopologicalBasis_opens
  have h : ∀ (S : Set T) (hS : IsConstructible S),
      S.Nonempty → (S ∩ closedPoints T).Nonempty := by
    intro S hS
    induction S, hS using IsConstructible.induction_of_isTopologicalBasis
        (fun U : Opens T => (U : Set T)) hb (fun _ => NoetherianSpace.isCompact _) with
    | sdiff U A hA =>
      intro hn
      exact nonempty_inter_closedPoints hn
        (U.isOpen.isLocallyClosed.inter
          (isOpen_biUnion (fun V _ => V.isOpen)).isClosed_compl.isLocallyClosed)
    | union S hs T ht ihS ihT =>
      intro hn
      obtain ⟨x, hx⟩ := hn
      rcases hx with hxS | hxT
      · obtain ⟨y, hyS, hyC⟩ := ihS ⟨x, hxS⟩
        exact ⟨y, Or.inl hyS, hyC⟩
      · obtain ⟨y, hyT, hyC⟩ := ihT ⟨x, hxT⟩
        exact ⟨y, Or.inr hyT, hyC⟩
  obtain ⟨y, hyS, hyC⟩ := h S hS hne
  exact ⟨y, hyS, hyC⟩

end
end Negativity
