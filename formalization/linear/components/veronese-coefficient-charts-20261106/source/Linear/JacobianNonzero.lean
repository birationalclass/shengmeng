module
public import Linear.PolynomialApproximation
public import Linear.PolynomialSocle
public import Linear.DiagonalNonzero
public import Linear.ArtinianDiagonal
public import Linear.JacobianTrace
public import Linear.TensorDifference

/-!
# Nonzero actual multivariable derivative Jacobian and scalar socle

For zero-constant regular power-series equations over a characteristic-zero field, assume the actual quotient is Artinian and finite-dimensional. Prove that the actual derivative Jacobian is nonzero, scalar-generates its socle, and generates the nilradical annihilator as an ideal. Polynomial unit changes, the universal difference matrix and actual algebraic trace supply nonvanishing; no Jacobian/socle identity is an input. The relative theorem and arbitrary parameter lifts remain unproved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000
open scoped TensorProduct
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

theorem powerSeriesQuotient_polynomial_diagonal
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hpzero : ∀ i, (P i).constantCoeff = 0)
    (hp : ∀ i, Ideal.Quotient.mk (Ideal.span (Set.range H))
      (P i : MvPowerSeries (Fin (n + 1)) K) = 0) :
    let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
    let q := Ideal.Quotient.mk (Ideal.span (Set.range H))
    ∃ N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) K),
      N.mulVec MvPowerSeries.X = (fun i => (P i : MvPowerSeries (Fin (n + 1)) K)) ∧
      ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Q ⊗[K] Q),
        Annihilates (KaehlerDifferential.ideal K Q) M.det ∧
        Algebra.TensorProduct.lmul' K M.det =
          Matrix.det (fun i j => q ((MvPolynomial.pderiv j (P i) :
            MvPolynomial (Fin (n + 1)) K) : MvPowerSeries (Fin (n + 1)) K)) ∧
        pairingRightReduction (powerSeriesQuotientAugmentation H hzero) M.det = q N.det := by
  classical
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
  let q := Ideal.Quotient.mkₐ K (Ideal.span (Set.range H))
  let s := polynomialDoubleTensor q
  let a := powerSeriesQuotientAugmentation H hzero
  obtain ⟨D, hD, hdiag, hN⟩ := polynomial_universal_difference_matrix P hpzero
  let N := D.map polynomialDoubleRightZero
  let M := D.map s
  have hp' : ∀ i, q (P i : MvPowerSeries (Fin (n + 1)) K) = 0 := hp
  have hM : M.mulVec (fun i => q (MvPowerSeries.X i) ⊗ₜ[K] (1 : Q) -
      (1 : Q) ⊗ₜ[K] q (MvPowerSeries.X i)) = 0 := by
    funext i
    have h := congrArg s (congrFun hD i)
    simp only [s, Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub,
      polynomialDoubleTensor_left, polynomialDoubleTensor_right, hp',
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, sub_self] at h
    change (∑ j, s (D i j) * (q (MvPowerSeries.X j) ⊗ₜ[K] (1 : Q) -
      (1 : Q) ⊗ₜ[K] q (MvPowerSeries.X j))) = 0
    simpa [s, polynomialDoubleTensor] using h
  have hideal := powerSeries_tensor_diagonal_eq_coordinate_ideal q
    Ideal.Quotient.mk_surjective (fun i => powerSeriesQuotient_variable_nilpotent H hzero i)
  refine ⟨N, hN, M, ?_, ?_, ?_⟩
  · rw [← hideal]
    exact determinant_annihilates_coordinate_ideal M _ hM
  · let J : Matrix (Fin (n + 1)) (Fin (n + 1)) Q :=
      fun i j => q ((MvPolynomial.pderiv j (P i) : MvPolynomial (Fin (n + 1)) K) :
        MvPowerSeries (Fin (n + 1)) K)
    have hd : Algebra.TensorProduct.lmul' K M.det =
        (M.map (Algebra.TensorProduct.lmul' K : Q ⊗[K] Q →ₐ[K] Q)).det :=
      (Algebra.TensorProduct.lmul' K).map_det M
    refine hd.trans ?_
    congr 1
    ext i j
    change Algebra.TensorProduct.lmul' K (s (D i j)) = _
    rw [polynomialDoubleTensor_multiplication, hdiag]
    rfl
  · change (pairingRightReduction a).toRingHom M.det = q.toRingHom N.det
    rw [(pairingRightReduction a).toRingHom.map_det, q.toRingHom.map_det]
    congr 1
    ext i j
    change pairingRightReduction a (s (D i j)) = q (polynomialDoubleRightZero (D i j))
    exact polynomialDoubleTensor_rightReduction q a (by intro i; simp [a, q]) _

theorem powerSeriesQuotient_jacobian_nonzero [CharZero K]
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    powerSeriesJacobianClass H ≠ 0 := by
  classical
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)
  let q := Ideal.Quotient.mk (Ideal.span (Set.range H))
  let a := powerSeriesQuotientAugmentation H hzero
  let : Nontrivial Q := a.toRingHom.domain_nontrivial
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  choose b hb using fun i => powerSeriesQuotient_variable_nilpotent H hzero i
  have hbmem : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin (n + 1)) K) ^ b i ∈
      Ideal.span (Set.range H) := by
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow] using hb i
  obtain ⟨P, hP, U, hU, hUP, hU0⟩ := powerSeries_polynomial_equations_unit_change H b hbmem
  have hpzero : ∀ i, (P i).constantCoeff = 0 := by
    intro i
    change (P i).coeff 0 = 0
    rw [hP]
    simp [MvPowerSeries.coeff_trunc', hzero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hp : ∀ i, q (P i : MvPowerSeries (Fin (n + 1)) K) = 0 := by
    intro i
    rw [← congrFun hUP i]
    change q (∑ j, U i j * H j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_mul, show q (H j) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self j)), mul_zero]
  obtain ⟨N, hN, M, hM, hmu, hred⟩ := powerSeriesQuotient_polynomial_diagonal H hzero P hpzero hp
  have hn0 := powerSeries_unit_changed_coefficientDeterminant_ne_zero H hH hzero U N hU
    (hUP.trans hN.symm)
  obtain ⟨C, hC, p, hpC⟩ := powerSeries_completeIntersection_perfectPairing H hH hzero
  have hmax : RingHom.ker a.toRingHom = IsLocalRing.maximalIdeal Q :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective a.toRingHom
      (powerSeriesQuotientAugmentation_surjective H hzero))
  have hnon := diagonal_annihilator_multiplication_nonzero a hmax p M.det hM
    (by rw [hred]; exact hn0)
  have he : Matrix.det (fun i j => q ((MvPolynomial.pderiv j (P i) :
      MvPolynomial (Fin (n + 1)) K) : MvPowerSeries (Fin (n + 1)) K)) =
      powerSeriesJacobianClass H := by
    rw [show powerSeriesJacobianClass H =
      Matrix.det (fun i j => q (MvPowerSeries.pderiv j (H i))) from q.map_det _]
    congr 1
    ext i j
    rw [hP]
    exact (powerSeries_map_pderiv_eq_trunc_of_nilpotent q b hb (H i) j).symm
  rwa [hmu, he] at hnon

theorem powerSeriesQuotient_jacobian_scalar_socle [CharZero K]
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    (x : MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H)) :
    Annihilates (nilradical (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))) x ↔
      ∃ b : K, x = b • powerSeriesJacobianClass H := by
  let a := powerSeriesQuotientAugmentation H hzero
  obtain ⟨C, hC, p, hpC⟩ := powerSeries_completeIntersection_perfectPairing H hH hzero
  have hJ := powerSeriesQuotient_jacobian_annihilates_nilradical H hH hzero
  have hJ' : Annihilates (RingHom.ker a.toRingHom) (powerSeriesJacobianClass H) := by
    rwa [powerSeriesQuotientAugmentation_kernel_nilradical]
  have hf : p.functional (powerSeriesJacobianClass H) ≠ 0 := by
    intro hz
    have h := annihilator_eq_scalar_generator a p hJ'
    rw [hz, zero_smul] at h
    exact powerSeriesQuotient_jacobian_nonzero H hH hzero h
  have h := unit_coefficient_generates_annihilator a p (powerSeriesJacobianClass H)
    hJ' (isUnit_iff_ne_zero.mpr hf) x
  rwa [powerSeriesQuotientAugmentation_kernel_nilradical] at h

theorem powerSeriesQuotient_jacobian_socle [CharZero K]
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K)
    (hH : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin (n + 1)) K) (List.ofFn H))
    (hzero : ∀ i, (H i).constantCoeff = 0)
    [IsArtinianRing (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))]
    [FiniteDimensional K (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))] :
    (nilradical (MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range H))).annihilator =
      Ideal.span {powerSeriesJacobianClass H} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, rfl⟩ := (powerSeriesQuotient_jacobian_scalar_socle H hH hzero x).mp
      ((annihilates_iff_mem_annihilator _ _).mpr hx)
    exact Submodule.smul_of_tower_mem (Ideal.span {powerSeriesJacobianClass H}) b
      (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = powerSeriesJacobianClass H)
    exact (annihilates_iff_mem_annihilator _ _).mp
      (powerSeriesQuotient_jacobian_annihilates_nilradical H hH hzero)

end LinearStudy
