module
public import Linear.UniversalDifference
public import Linear.DiagonalTrace

/-!
# Actual tensor specializations of the universal polynomial difference

The two sets of polynomial variables map into the two factors of the actual algebra tensor product. Tensor multiplication and right augmentation commute with the diagonal and right-zero substitutions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace LinearStudy
variable {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]

def polynomialDoubleTensor (q : MvPowerSeries ι K →ₐ[K] A) :
    MvPolynomial (ι ⊕ ι) K →ₐ[K] A ⊗[K] A :=
  MvPolynomial.aeval (Sum.elim
    (fun i => q (MvPowerSeries.X i) ⊗ₜ[K] (1 : A))
    (fun i => (1 : A) ⊗ₜ[K] q (MvPowerSeries.X i)))

theorem polynomialDoubleTensor_left (q : MvPowerSeries ι K →ₐ[K] A)
    (P : MvPolynomial ι K) :
    polynomialDoubleTensor q (MvPolynomial.rename Sum.inl P) =
      q (P : MvPowerSeries ι K) ⊗ₜ[K] (1 : A) := by
  let l : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeLeft
  have h : (polynomialDoubleTensor q).toRingHom.comp
      (MvPolynomial.rename Sum.inl).toRingHom =
      l.toRingHom.comp (q.toRingHom.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    have hqc : ∀ c, q (MvPowerSeries.C c) = algebraMap K A c := by
      intro c; simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensor, l, hqc]
    · intro i; simp [polynomialDoubleTensor, l]
  exact RingHom.congr_fun h P

theorem polynomialDoubleTensor_right (q : MvPowerSeries ι K →ₐ[K] A)
    (P : MvPolynomial ι K) :
    polynomialDoubleTensor q (MvPolynomial.rename Sum.inr P) =
      (1 : A) ⊗ₜ[K] q (P : MvPowerSeries ι K) := by
  let r : A →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.includeRight
  have h : (polynomialDoubleTensor q).toRingHom.comp
      (MvPolynomial.rename Sum.inr).toRingHom =
      r.toRingHom.comp (q.toRingHom.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    have hqc : ∀ c, q (MvPowerSeries.C c) = algebraMap K A c := by
      intro c; simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensor, r, hqc]
    · intro i; simp [polynomialDoubleTensor, r]
  exact RingHom.congr_fun h P

theorem polynomialDoubleTensor_multiplication (q : MvPowerSeries ι K →ₐ[K] A)
    (P : MvPolynomial (ι ⊕ ι) K) :
    Algebra.TensorProduct.lmul' K (polynomialDoubleTensor q P) =
      q ((polynomialDoubleDiagonal P : MvPolynomial ι K) : MvPowerSeries ι K) := by
  have h : (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A).toRingHom.comp
      (polynomialDoubleTensor q).toRingHom =
      q.toRingHom.comp (MvPolynomial.coeToMvPowerSeries.ringHom.comp
        polynomialDoubleDiagonal) := by
    have hqc : ∀ c, q (MvPowerSeries.C c) = algebraMap K A c := by
      intro c; simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensor, polynomialDoubleDiagonal,
        hqc]
    · intro i; cases i <;> simp [polynomialDoubleTensor, polynomialDoubleDiagonal]
  exact RingHom.congr_fun h P

theorem polynomialDoubleTensor_rightReduction
    (q : MvPowerSeries ι K →ₐ[K] A) (a : A →ₐ[K] K)
    (ha : ∀ i, a (q (MvPowerSeries.X i)) = 0)
    (P : MvPolynomial (ι ⊕ ι) K) :
    pairingRightReduction a (polynomialDoubleTensor q P) =
      q (polynomialDoubleRightZero P) := by
  have h : (pairingRightReduction a).toRingHom.comp
      (polynomialDoubleTensor q).toRingHom =
      q.toRingHom.comp polynomialDoubleRightZero := by
    have hqc : ∀ c, q (MvPowerSeries.C c) = algebraMap K A c := by
      intro c; simpa [MvPowerSeries.algebraMap_apply] using q.commutes c
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensor, polynomialDoubleRightZero,
        hqc, pairingRightReduction_tmul]
    · intro i; cases i <;>
        simp [polynomialDoubleTensor, polynomialDoubleRightZero,
          pairingRightReduction_tmul, ha]
  exact RingHom.congr_fun h P

end LinearStudy
