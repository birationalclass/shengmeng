module
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section
open scoped DirectSum
universe u v w
namespace Negativity
noncomputable section
variable (R : Type u) [Semiring R] (κ : Type v) (ι : Type w) [Fintype ι]
    (M : κ → ι → Type*) [∀ n j, AddCommMonoid (M n j)] [∀ n j, Module R (M n j)]

/-- Finite chart products commute with the direct sum of homogeneous pieces.
All substantive isomorphisms here are existing Mathlib DirectSum APIs. -/
def finitePiDirectSumLinearEquiv :
    (⨁ n : κ, ∀ j : ι, M n j) ≃ₗ[R] ∀ j : ι, ⨁ n : κ, M n j := by
  classical
  let swap : (Σ _ : κ, ι) ≃ (Σ _ : ι, κ) :=
    { toFun := fun p => ⟨p.2, p.1⟩
      invFun := fun p => ⟨p.2, p.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (DirectSum.congrLinearEquiv (fun n =>
      (DirectSum.linearEquivFunOnFintype R ι (M n)).symm)).trans
    ((DirectSum.sigmaLcurryEquiv R).symm.trans
    ((DirectSum.lequivCongrLeft R swap).trans
    ((DirectSum.sigmaLcurryEquiv R).trans
      (DirectSum.linearEquivFunOnFintype R ι (fun j => ⨁ n : κ, M n j)))))

@[simp]
theorem finitePiDirectSumLinearEquiv_apply
    (x : ⨁ n : κ, ∀ j : ι, M n j) (j : ι) (n : κ) :
    finitePiDirectSumLinearEquiv R κ ι M x j n = x n j := by
  classical
  simp [finitePiDirectSumLinearEquiv, DirectSum.congrLinearEquiv,
    DirectSum.sigmaLcurryEquiv, DirectSum.linearEquivFunOnFintype,
    DirectSum.lequivCongrLeft, DFinsupp.sigmaCurryLEquiv,
    DFinsupp.linearEquivFunOnFintype, DFinsupp.sigmaCurryEquiv,
    DFinsupp.domLCongr, DFinsupp.equivFunOnFintype, DirectSum.congrAddEquiv,
    DirectSum.map]
  rfl

#print axioms finitePiDirectSumLinearEquiv
#print axioms finitePiDirectSumLinearEquiv_apply
end
end Negativity
