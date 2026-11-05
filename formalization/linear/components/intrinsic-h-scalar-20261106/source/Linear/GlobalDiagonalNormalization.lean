module

public import Linear.DiagonalNormalization
public import Linear.ArtinianGlobalPairing
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
namespace LinearStudy
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

theorem diagonal_coefficient_notMem_kernel
    (q : A →ₐ[K] K) (p : PerfectMultiplicationPairing (B := K) (A := A))
    (d : A ⊗[K] A) (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : pairingRightReduction q d ≠ 0) :
    pairingTensorEndEquiv p d 1 ∉ RingHom.ker q.toRingHom := by
  let c := pairingTensorEndEquiv p d 1
  have h : pairingRightReduction q d = c * dualGenerator q p := by
    rw [pairingDiagonal_generates_annihilator p d hd, map_mul,
      pairingRightReduction_diagonal, pairingRightReduction_tmul, map_one, one_smul]
  intro hc
  exact hred (h.trans (dualGenerator_annihilates q p c hc))

theorem global_diagonal_coefficient_isUnit
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal)
    (p : PerfectMultiplicationPairing (B := K) (A := A))
    (d : A ⊗[K] A) (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : ∀ j, pairingRightReduction (q j) d ≠ 0) :
    IsUnit (pairingTensorEndEquiv p d 1) := by
  by_contra hc
  have hspan : Ideal.span {pairingTensorEndEquiv p d 1} ≠ ⊤ := by
    intro ht
    exact hc (Ideal.span_singleton_eq_top.mp ht)
  obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hspan
  let j : MaximalSpectrum A := ⟨I, hI⟩
  apply diagonal_coefficient_notMem_kernel (q j) p d hd (hred j)
  rw [hq]
  exact hle (Ideal.subset_span (Set.mem_singleton _))

theorem global_diagonal_unique_functional
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal)
    (p : PerfectMultiplicationPairing (B := K) (A := A))
    (d : A ⊗[K] A) (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : ∀ j, pairingRightReduction (q j) d ≠ 0) :
    ∃! ell : A →ₗ[K] K, tensorFunctionalContraction ell d = 1 :=
  diagonal_tensor_unique_functional p d hd (global_diagonal_coefficient_isUnit q hq p d hd hred)

theorem global_diagonal_normalized_trace
    (q : MaximalSpectrum A → A →ₐ[K] K)
    (hq : ∀ j, RingHom.ker (q j).toRingHom = j.asIdeal)
    (p : PerfectMultiplicationPairing (B := K) (A := A))
    (d : A ⊗[K] A) (hd : Annihilates (KaehlerDifferential.ideal K A) d)
    (hred : ∀ j, pairingRightReduction (q j) d ≠ 0) :
    ∃ p' : PerfectMultiplicationPairing (B := K) (A := A),
      pairingDiagonal p' = d ∧ ∀ a : A,
        p'.functional (a * Algebra.TensorProduct.lmul' K d) = Algebra.trace K A a :=
  normalized_diagonal_residue_trace p d hd (global_diagonal_coefficient_isUnit q hq p d hd hred)

end LinearStudy
