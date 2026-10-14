module
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.DFinsupp
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
variable (P : I → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

/-- Canonical finite-family dual assembly,using mathlib's original
DFinsupp universal map and finite function equivalence. No dimension
hypothesis or independently supplied dual comparison is used. -/
def finitePiDualEquiv : (∀ i, Module.Dual R (P i)) ≃ₗ[R] Module.Dual R (∀ i, P i) :=
  (DFinsupp.lsum R).trans
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := P)).symm.dualMap

/-- The original assembled functional restricts to its original
component on each original coordinate inclusion. -/
theorem finitePiDualEquiv_single (φ : ∀ i, Module.Dual R (P i)) (i : I) (x : P i) :
    finitePiDualEquiv P φ (Pi.single i x) = φ i x := by
  simp only [finitePiDualEquiv,LinearEquiv.trans_apply,LinearEquiv.dualMap_apply,
    DFinsupp.linearEquivFunOnFintype_symm_apply,DFinsupp.equivFunOnFintype_symm_single,
    DFinsupp.lsum_single]

/-- Actual finite-family pairing is the sum of the actual original
component pairings. This will match the original dual-entry matrix. -/
theorem finitePiDualEquiv_apply (φ : ∀ i, Module.Dual R (P i)) (x : ∀ i, P i) :
    finitePiDualEquiv P φ x = ∑ i, φ i (x i) := by
  have hx : x = ∑ i, Pi.single i (x i) := (LinearMap.sum_single_apply P x).symm
  calc
    finitePiDualEquiv P φ x = finitePiDualEquiv P φ (∑ i, Pi.single i (x i)) := congrArg (finitePiDualEquiv P φ) hx
    _ = ∑ i, finitePiDualEquiv P φ (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, φ i (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact finitePiDualEquiv_single P φ i (x i)

end LinearStudy
