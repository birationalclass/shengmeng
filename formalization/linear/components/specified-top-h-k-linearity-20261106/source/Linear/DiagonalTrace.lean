module
public import Linear.TraceElement
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Actual diagonal element and algebraic trace of a perfect pairing

Construct the tensor/endomorphism equivalence from a perfect multiplication
pairing, and the diagonal element corresponding to the identity. Prove
that it annihilates the actual diagonal ideal, scalar-generates that
annihilator and maps under multiplication to the actual algebraic trace
element. A supplied pairing is explicit; no Jacobian identification or
normalization of the difference determinant is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace LinearStudy
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

def pairingTensorEndEquiv (p : PerfectMultiplicationPairing (B := R) (A := A)) :
    A ⊗[R] A ≃ₗ[R] Module.End R A :=
  (TensorProduct.congr p.equiv (LinearEquiv.refl R A)).trans (dualTensorHomEquiv R A A)

theorem pairingTensorEndEquiv_tmul
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (x y a : A) :
    pairingTensorEndEquiv p (x ⊗ₜ[R] y) a = p.functional (x * a) • y := by
  simp [pairingTensorEndEquiv, p.equiv_apply]

theorem pairingTensorEndEquiv_left
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A) (x a : A) :
    pairingTensorEndEquiv p ((x ⊗ₜ[R] (1 : A)) * d) a =
      pairingTensorEndEquiv p d (x * a) := by
  induction d using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pairingTensorEndEquiv_tmul]
    congr 2; ring
  | add d e hd he =>
    simp only [mul_add, map_add, LinearMap.add_apply, hd, he]

theorem pairingTensorEndEquiv_right
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A) (x a : A) :
    pairingTensorEndEquiv p (((1 : A) ⊗ₜ[R] x) * d) a =
      x * pairingTensorEndEquiv p d a := by
  induction d using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pairingTensorEndEquiv_tmul]
    exact (mul_smul_comm (p.functional (y * a)) x z).symm
  | add d e hd he =>
    simp only [mul_add, map_add, LinearMap.add_apply, hd, he]

def pairingDiagonal (p : PerfectMultiplicationPairing (B := R) (A := A)) : A ⊗[R] A :=
  (pairingTensorEndEquiv p).symm LinearMap.id

theorem pairingDiagonal_annihilates
    (p : PerfectMultiplicationPairing (B := R) (A := A)) :
    Annihilates (KaehlerDifferential.ideal R A) (pairingDiagonal p) := by
  rw [annihilates_iff_mem_annihilator, ← KaehlerDifferential.span_range_eq_ideal]
  apply Submodule.mem_annihilator.mpr
  intro z hz
  change pairingDiagonal p * z = 0
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    apply (pairingTensorEndEquiv p).injective
    rw [map_zero]
    ext a
    rw [mul_comm, sub_mul, map_sub, LinearMap.sub_apply,
      pairingTensorEndEquiv_right, pairingTensorEndEquiv_left]
    simp [pairingDiagonal]
  | zero => simp
  | add z w hz hw hd he => simp [mul_add, hd, he]
  | smul c z hz hd =>
    change pairingDiagonal p * (c * z) = 0
    calc
      _ = c * (pairingDiagonal p * z) := by ring
      _ = 0 := by rw [hd, mul_zero]

theorem pairingTensorEndEquiv_trace
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A) :
    LinearMap.trace R A (pairingTensorEndEquiv p d) =
      p.functional (Algebra.TensorProduct.lmul' R d) := by
  unfold pairingTensorEndEquiv
  rw [LinearEquiv.trans_apply]
  change LinearMap.trace R A (dualTensorHom R A A
    (TensorProduct.congr p.equiv (LinearEquiv.refl R A) d)) = _
  rw [LinearMap.trace_eq_contract_apply]
  induction d using TensorProduct.inductionOn with
  | tmul x y => simp [p.equiv_apply]
  | add d e hd he => simp only [map_add, hd, he]

theorem pairingDiagonal_multiplication_eq_traceElement
    (p : PerfectMultiplicationPairing (B := R) (A := A)) :
    Algebra.TensorProduct.lmul' R (pairingDiagonal p) = traceElement p := by
  apply eq_traceElement_of_residue_trace p
  intro a
  have h := pairingTensorEndEquiv_trace p ((a ⊗ₜ[R] (1 : A)) * pairingDiagonal p)
  have he : pairingTensorEndEquiv p ((a ⊗ₜ[R] (1 : A)) * pairingDiagonal p) =
      Algebra.lmul R A a := by
    ext b
    rw [pairingTensorEndEquiv_left]
    simp [pairingDiagonal]
  rw [he] at h
  simpa [Algebra.trace_apply, mul_comm] using h.symm

theorem pairingTensorEndEquiv_of_diagonal_annihilator
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d) :
    pairingTensorEndEquiv p d = Algebra.lmul R A (pairingTensorEndEquiv p d 1) := by
  ext a
  have hz := hd ((1 : A) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : A))
    (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (S := A) R a)
  have he := congrArg (fun z => pairingTensorEndEquiv p z (1 : A)) hz
  rw [sub_mul, map_sub, LinearMap.sub_apply, pairingTensorEndEquiv_right,
    pairingTensorEndEquiv_left, mul_one, map_zero, LinearMap.zero_apply,
    sub_eq_zero] at he
  change pairingTensorEndEquiv p d a = pairingTensorEndEquiv p d 1 * a
  exact he.symm.trans (mul_comm _ _)

theorem pairingDiagonal_generates_annihilator
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d) :
    d = ((pairingTensorEndEquiv p d 1) ⊗ₜ[R] (1 : A)) * pairingDiagonal p := by
  apply (pairingTensorEndEquiv p).injective
  ext a
  rw [pairingTensorEndEquiv_left, pairingDiagonal,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  have h := LinearMap.congr_fun (pairingTensorEndEquiv_of_diagonal_annihilator p d hd) a
  exact h

theorem diagonal_annihilator_multiplication_eq_trace_multiple
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d) :
    Algebra.TensorProduct.lmul' R d =
      pairingTensorEndEquiv p d 1 * traceElement p := by
  have h := congrArg (Algebra.TensorProduct.lmul' R)
    (pairingDiagonal_generates_annihilator p d hd)
  simpa only [map_mul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
    pairingDiagonal_multiplication_eq_traceElement] using h

def pairingRightReduction (q : A →ₐ[R] R) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (AlgHom.id R A) ((Algebra.ofId R A).comp q)
    (fun _ _ => Commute.all _ _)

omit [Module.Free R A] [Module.Finite R A] in
theorem pairingRightReduction_tmul (q : A →ₐ[R] R) (x y : A) :
    pairingRightReduction q (x ⊗ₜ[R] y) = (q y) • x := by
  simp [pairingRightReduction, Algebra.smul_def, mul_comm]

theorem pairingRightReduction_pairing
    (q : A →ₐ[R] R) (p : PerfectMultiplicationPairing (B := R) (A := A))
    (d : A ⊗[R] A) (a : A) :
    p.functional (a * pairingRightReduction q d) = q (pairingTensorEndEquiv p d a) := by
  induction d using TensorProduct.inductionOn with
  | tmul x y =>
    rw [pairingRightReduction_tmul, pairingTensorEndEquiv_tmul, mul_smul_comm,
      map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [mul_comm x a, mul_comm]
  | add d e hd he =>
    simp only [map_add, mul_add, LinearMap.add_apply, hd, he]

theorem pairingRightReduction_diagonal
    (q : A →ₐ[R] R) (p : PerfectMultiplicationPairing (B := R) (A := A)) :
    pairingRightReduction q (pairingDiagonal p) = dualGenerator q p := by
  apply p.equiv.injective
  ext a
  rw [p.equiv_apply, p.equiv_apply, dualGenerator_pairing, mul_comm,
    pairingRightReduction_pairing]
  simp [pairingDiagonal]

end LinearStudy
