module
public import Linear.DiagonalNormalization
public import Linear.PairingMatrix
public import Mathlib.Tactic
/-! A diagonal tensor annihilating the actual Kaehler ideal and normalized by contraction constructs a perfect multiplication pairing over a finite-dimensional algebra. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem tensorFunctionalContraction_left
    (ell : A →ₗ[K] K) (d : A ⊗[K] A) (x : A) :
    tensorFunctionalContraction ell ((x ⊗ₜ[K] (1 : A)) * d) =
      tensorFunctionalContraction (multiplicationToDual ell x) d := by
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tensorFunctionalContraction_tmul]
    rfl
  | add d e hd he => simp only [mul_add, map_add, hd, he]

theorem tensorFunctionalContraction_right
    (ell : A →ₗ[K] K) (d : A ⊗[K] A) (x : A) :
    tensorFunctionalContraction ell (((1 : A) ⊗ₜ[K] x) * d) =
      x * tensorFunctionalContraction ell d := by
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tensorFunctionalContraction_tmul]
    exact (mul_smul_comm (ell a) x b).symm
  | add d e hd he => simp only [mul_add, map_add, mul_add, hd, he]

theorem normalized_contraction_multiplicationToDual_injective
    (ell : A →ₗ[K] K) (d : A ⊗[K] A)
    (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hn : tensorFunctionalContraction ell d = 1) :
    Function.Injective (multiplicationToDual ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hz := hd ((1 : A) ⊗ₜ[K] x - x ⊗ₜ[K] (1 : A))
    (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (S := A) K x)
  have he := congrArg (tensorFunctionalContraction ell) hz
  rw [sub_mul, map_sub, tensorFunctionalContraction_right,
    tensorFunctionalContraction_left, hx, hn, mul_one, map_zero] at he
  simpa [tensorFunctionalContraction] using he

def perfectPairingOfNormalizedContraction [FiniteDimensional K A]
    (ell : A →ₗ[K] K) (d : A ⊗[K] A)
    (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hn : tensorFunctionalContraction ell d = 1) :
    PerfectMultiplicationPairing (B := K) (A := A) where
  functional := ell
  equiv := LinearEquiv.ofInjectiveOfFinrankEq (multiplicationToDual ell)
    (normalized_contraction_multiplicationToDual_injective ell d hd hn)
    Subspace.dual_finrank_eq.symm
  equiv_apply := by intro x a; rfl

theorem normalized_contraction_pairing_diagonal [FiniteDimensional K A]
    (ell : A →ₗ[K] K) (d : A ⊗[K] A)
    (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hn : tensorFunctionalContraction ell d = 1) :
    pairingDiagonal (perfectPairingOfNormalizedContraction ell d hd hn) = d := by
  let p := perfectPairingOfNormalizedContraction ell d hd hn
  apply (pairingTensorEndEquiv p).injective
  rw [pairingDiagonal, LinearEquiv.apply_symm_apply,
    pairingTensorEndEquiv_of_diagonal_annihilator p d hd]
  have hp : p.equiv 1 = ell := by ext a; simp [p.equiv_apply, p]; rfl
  have he := tensorFunctionalContraction_pairing p d 1
  rw [hp, hn] at he
  rw [← he]
  ext a
  simp

end LinearStudy
