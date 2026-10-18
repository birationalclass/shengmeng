module
public import Linear.DiagonalTrace
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# DiagonalNonzero

For a finite local algebra with an explicit perfect pairing, a diagonal annihilator whose right augmentation is nonzero has unit coefficient relative to the pairing diagonal. In characteristic zero its multiplication image is nonzero. The nonzero right augmentation is an explicit input here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A] [IsLocalRing A]

theorem diagonal_annihilator_coefficient_isUnit
    (q : A →ₐ[K] K) (hq : RingHom.ker q.toRingHom = IsLocalRing.maximalIdeal A)
    (p : PerfectMultiplicationPairing (B := K) (A := A)) (d : A ⊗[K] A)
    (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : pairingRightReduction q d ≠ 0) :
    IsUnit (pairingTensorEndEquiv p d 1) := by
  let c := pairingTensorEndEquiv p d 1
  have h : pairingRightReduction q d = c * dualGenerator q p := by
    rw [pairingDiagonal_generates_annihilator p d hd, map_mul,
      pairingRightReduction_diagonal, pairingRightReduction_tmul, map_one, one_smul]
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hc
  rw [← hq] at hc
  exact hred (h.trans (dualGenerator_annihilates q p c hc))

theorem diagonal_annihilator_multiplication_nonzero [CharZero K]
    (q : A →ₐ[K] K) (hq : RingHom.ker q.toRingHom = IsLocalRing.maximalIdeal A)
    (p : PerfectMultiplicationPairing (B := K) (A := A)) (d : A ⊗[K] A)
    (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : pairingRightReduction q d ≠ 0) :
    Algebra.TensorProduct.lmul' K d ≠ 0 := by
  rw [diagonal_annihilator_multiplication_eq_trace_multiple p d hd]
  have hc := diagonal_annihilator_coefficient_isUnit q hq p d hd hred
  intro hz
  exact traceElement_nonzero_over_field p
    (hc.mul_left_cancel (hz.trans (mul_zero _).symm))

end LinearStudy
