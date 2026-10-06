module

public import Linear.DiagonalNonzero
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
namespace LinearStudy
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

def tensorFunctionalContraction (ell : A →ₗ[R] R) : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap.comp (TensorProduct.map ell LinearMap.id)

@[simp] theorem tensorFunctionalContraction_tmul (ell : A →ₗ[R] R) (x y : A) :
    tensorFunctionalContraction ell (x ⊗ₜ[R] y) = ell x • y := by
  simp [tensorFunctionalContraction]

variable [Module.Free R A] [Module.Finite R A]

theorem tensorFunctionalContraction_pairing
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A) (a : A) :
    tensorFunctionalContraction (p.equiv a) d = pairingTensorEndEquiv p d a := by
  induction d using TensorProduct.inductionOn with
  | tmul x y => simp [pairingTensorEndEquiv_tmul, p.equiv_apply, mul_comm]
  | add d e hd he => simp only [map_add, LinearMap.add_apply, hd, he]

def unitTwistedPairing (p : PerfectMultiplicationPairing (B := R) (A := A)) (u : Aˣ) :
    PerfectMultiplicationPairing (B := R) (A := A) where
  functional := p.functional.comp (u.mulLeftLinearEquiv R A).toLinearMap
  equiv := (u.mulLeftLinearEquiv R A).trans p.equiv
  equiv_apply x a := by
    change p.equiv ((u : A) * x) a = p.functional ((u : A) * (x * a))
    rw [p.equiv_apply, mul_assoc]

omit [Module.Free R A] [Module.Finite R A] in
@[simp] theorem unitTwistedPairing_functional
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (u : Aˣ) (a : A) :
    (unitTwistedPairing p u).functional a = p.functional ((u : A) * a) := rfl

theorem pairingTensorEndEquiv_unitTwisted
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (u : Aˣ)
    (d : A ⊗[R] A) (a : A) :
    pairingTensorEndEquiv (unitTwistedPairing p u) d a =
      pairingTensorEndEquiv p d ((u : A) * a) := by
  induction d using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [pairingTensorEndEquiv_tmul, unitTwistedPairing_functional]
    congr 2
    ring
  | add d e hd he => simp only [map_add, LinearMap.add_apply, hd, he]

theorem diagonal_tensor_normalized_pairing
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d)
    (hc : IsUnit (pairingTensorEndEquiv p d 1)) :
    ∃ p' : PerfectMultiplicationPairing (B := R) (A := A),
      pairingDiagonal p' = d ∧ tensorFunctionalContraction p'.functional d = 1 := by
  obtain ⟨u, hu⟩ := hc
  let p' := unitTwistedPairing p u⁻¹
  have he : pairingTensorEndEquiv p' d = LinearMap.id := by
    ext a
    rw [pairingTensorEndEquiv_unitTwisted]
    have h := LinearMap.congr_fun
      (pairingTensorEndEquiv_of_diagonal_annihilator p d hd) ((u⁻¹ : Aˣ) * a)
    change _ = a
    rw [h]
    change pairingTensorEndEquiv p d 1 * ((u⁻¹ : Aˣ) * a) = a
    rw [← hu]
    simp [← mul_assoc]
  refine ⟨p', ?_, ?_⟩
  · apply (pairingTensorEndEquiv p').injective
    simp [pairingDiagonal, he]
  · have hp : p'.equiv 1 = p'.functional := by
      ext a
      simp [p'.equiv_apply]
    rw [← hp, tensorFunctionalContraction_pairing, he]
    rfl

theorem diagonal_tensor_unique_functional
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d)
    (hc : IsUnit (pairingTensorEndEquiv p d 1)) :
    ∃! ell : A →ₗ[R] R, tensorFunctionalContraction ell d = 1 := by
  obtain ⟨p', hdiag, hnorm⟩ := diagonal_tensor_normalized_pairing p d hd hc
  refine ⟨p'.functional, hnorm, ?_⟩
  intro ell hell
  obtain ⟨a, rfl⟩ := p'.equiv.surjective ell
  have ha : a = 1 := by
    rw [tensorFunctionalContraction_pairing, ← hdiag, pairingDiagonal,
      LinearEquiv.apply_symm_apply] at hell
    exact hell
  subst a
  ext x
  simp [p'.equiv_apply]

theorem normalized_diagonal_residue_trace
    (p : PerfectMultiplicationPairing (B := R) (A := A)) (d : A ⊗[R] A)
    (hd : Annihilates (KaehlerDifferential.ideal R A) d)
    (hc : IsUnit (pairingTensorEndEquiv p d 1)) :
    ∃ p' : PerfectMultiplicationPairing (B := R) (A := A),
      pairingDiagonal p' = d ∧ ∀ a : A,
        p'.functional (a * Algebra.TensorProduct.lmul' R d) = Algebra.trace R A a := by
  obtain ⟨p', hdiag, _⟩ := diagonal_tensor_normalized_pairing p d hd hc
  refine ⟨p', hdiag, ?_⟩
  intro a
  rw [← hdiag, pairingDiagonal_multiplication_eq_traceElement]
  simpa only [mul_comm] using traceElement_pairing p' a

end LinearStudy
