module
public import Linear.PolynomialContraction
public import Linear.TopDeterminant
public import Linear.ContractionPairing
public import Linear.PolynomialDifferenceDegree
public import Mathlib.Tactic
/-! An actual affine perfect multiplication pairing has both low-degree vanishing and the derivative Jacobian trace formula. Positive-degree regular highest parts and origin-only highest zero locus are explicit hypotheses. Geometric residue and projective fiber comparisons remain unproved. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace LinearStudy
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem polynomial_difference_matrix_right_zero
    (P : ι → MvPolynomial ι K)
    (D : Matrix ι ι (MvPolynomial (ι ⊕ ι) K))
    (hD : D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
      (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i))) :
    Matrix.mulVec (fun i j => polynomialDoubleRightPoint (0 : ι → K) (D i j)) MvPolynomial.X =
      fun i => P i - MvPolynomial.C ((P i).constantCoeff) := by
  funext i
  have hh := congrArg (polynomialDoubleRightPoint (0 : ι → K)) (congrFun hD i)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub,
    polynomialDoubleRightPoint_left, polynomialDoubleRightPoint_right, MvPolynomial.eval_zero] at hh
  simpa [Matrix.mulVec, dotProduct, polynomialDoubleRightPoint] using hh

theorem polynomial_difference_matrix_diagonal
    (P : ι → MvPolynomial ι K)
    (D : Matrix ι ι (MvPolynomial (ι ⊕ ι) K))
    (hD : D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
      (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)))
    (hd : ∀ i j, polynomialDoubleDiagonal (D i j) = MvPolynomial.pderiv j (P i)) :
    let Q := MvPolynomial ι K ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    Annihilates (KaehlerDifferential.ideal K Q) (polynomialDoubleTensorMap P D.det) ∧
      Algebra.TensorProduct.lmul' K (polynomialDoubleTensorMap P D.det) =
        Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i))) := by
  classical
  let Q := MvPolynomial ι K ⧸ Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mkₐ K (Ideal.span (Set.range P))
  let phi := polynomialDoubleTensorMap P
  let M : Matrix ι ι (Q ⊗[K] Q) := fun i j => phi (D i j)
  have he : M.mulVec (fun i => pi (MvPolynomial.X i) ⊗ₜ[K] (1 : Q) -
      (1 : Q) ⊗ₜ[K] pi (MvPolynomial.X i)) = 0 := by
    funext i
    have hp : pi (P i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    have hh := congrArg phi (congrFun hD i)
    dsimp only [phi] at hh
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub,
      polynomialDoubleTensorMap_left, polynomialDoubleTensorMap_right] at hh
    change (∑ j, polynomialDoubleTensorMap P (D i j) *
      (polynomialDoubleTensorMap P (MvPolynomial.X (Sum.inl j)) -
        polynomialDoubleTensorMap P (MvPolynomial.X (Sum.inr j)))) =
      pi (P i) ⊗ₜ[K] (1 : Q) - (1 : Q) ⊗ₜ[K] pi (P i) at hh
    rw [hp] at hh
    simpa [M, phi, pi, Matrix.mulVec, dotProduct, polynomialDoubleTensorMap] using hh
  have hdet : phi D.det = M.det :=
    RingHom.map_det (S := Q ⊗[K] Q) phi.toRingHom D
  constructor
  · rw [hdet, ← polynomial_tensor_diagonal_eq_coordinate_ideal pi Ideal.Quotient.mk_surjective]
    exact determinant_annihilates_coordinate_ideal M _ he
  · rw [polynomialDoubleTensorMap_multiplication,
      RingHom.map_det polynomialDoubleDiagonal D,
      RingHom.map_det (Ideal.Quotient.mk (Ideal.span (Set.range P)))]
    congr 1
    funext i j
    change Ideal.Quotient.mk (Ideal.span (Set.range P)) (polynomialDoubleDiagonal (D i j)) = _
    rw [hd i j]

omit [Fintype ι] [DecidableEq ι] in
theorem affine_polynomial_low_degree_trace_pairing [IsAlgClosed K] [CharZero K] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    let I := Ideal.span (Set.range P)
    let Q := MvPolynomial (Fin (n + 1)) K ⧸ I
    let pi := Ideal.Quotient.mk I
    ∃ p : PerfectMultiplicationPairing (B := K) (A := Q),
      (∀ f : MvPolynomial (Fin (n + 1)) K,
        f.totalDegree < ∑ i, ((P i).totalDegree - 1) → p.functional (pi f) = 0) ∧
      ∀ a : Q, p.functional (a * Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i)))) =
        Algebra.trace K Q a := by
  classical
  let e := fun i => (P i).totalDegree
  let H := fun i => MvPolynomial.homogeneousComponent (e i) (P i)
  let B := ∑ i, (e i - 1)
  let I := Ideal.span (Set.range P)
  let Q := MvPolynomial (Fin (n + 1)) K ⧸ I
  let pi := Ideal.Quotient.mk I
  let J := Ideal.span (Set.range H)
  let QH := MvPolynomial (Fin (n + 1)) K ⧸ J
  let pj := Ideal.Quotient.mk J
  let q := polynomialOriginMap J hz
  let : Module.Finite K Q := polynomialQuotient_finite_of_top_zeroLocus P hz
  let : Module.Finite K QH := polynomialQuotient_finite_of_origin_zeroLocus J hz
  have hH : ∀ i, (H i).IsHomogeneous (e i) := fun _ =>
    MvPolynomial.homogeneousComponent_isHomogeneous _ _
  obtain ⟨pH, _, _, _⟩ := homogeneous_polynomial_low_degree_pairing H e he hH hreg hz
  obtain ⟨ell, hell, hv⟩ := affine_filtered_functional_descends P hreg B
    (affine_polynomial_bounded_normal_form P he hreg hz) pH.functional
  obtain ⟨D, hD, hder, hDdeg⟩ := polynomial_universal_difference_matrix_degree P
  let u := polynomialDoubleRightPoint (0 : Fin (n + 1) → K)
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
    fun i j => u (D i j)
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
    fun i j => MvPolynomial.homogeneousComponent (e i - 1) (N i j)
  have hNdeg : ∀ i j, (N i j).totalDegree ≤ e i - 1 := fun i j =>
    (polynomialDoubleRightZero_totalDegree (D i j)).trans (hDdeg i j)
  have hN := polynomial_difference_matrix_right_zero P D hD
  change N.mulVec MvPolynomial.X = (fun i => P i - MvPolynomial.C ((P i).constantCoeff)) at hN
  have hC : C.mulVec MvPolynomial.X = H := coefficient_matrix_top_equations P e he N hN
  have hq0 : ∀ i, q (pj (MvPolynomial.X i)) = 0 := by
    intro i
    change MvPolynomial.aeval (R := K) (0 : Fin (n + 1) → K) (MvPolynomial.X i) = 0
    simp
  have hne : pj C.det ≠ 0 := polynomial_coefficientDeterminant_ne_zero_at_point H hreg q C
    (by
      change C.mulVec (fun i => MvPolynomial.X i - MvPolynomial.C (q (pj (MvPolynomial.X i)))) = H
      simpa only [hq0, map_zero, sub_zero] using hC)
  have hcoord := polynomial_quotient_coordinateIdeal_eq_kernel H q
  change (Ideal.span (Set.range (fun i => MvPolynomial.X i -
    MvPolynomial.C (q (pj (MvPolynomial.X i)))))).map pj = RingHom.ker q.toRingHom at hcoord
  simp only [hq0, map_zero, sub_zero] at hcoord
  have hgen : (RingHom.ker q.toRingHom).annihilator = Ideal.span {pj C.det} := by
    rw [← hcoord]
    exact coordinate_annihilator_eq_coefficientDeterminant H MvPolynomial.X hreg
      (polynomial_variables_regular (n + 1)) C hC
  have hann : Annihilates (RingHom.ker q.toRingHom) (pj C.det) := by
    apply (annihilates_iff_mem_annihilator _ _).mpr
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnon := perfect_socle_functional_nonzero q pH (pj C.det) hann hne
  have hNdetdeg : N.det.totalDegree ≤ B := polynomial_matrix_det_degree N (fun i => e i - 1) hNdeg
  have hNtop : MvPolynomial.homogeneousComponent B N.det = C.det :=
    homogeneousComponent_det_top N (fun i => e i - 1) hNdeg
  let c := ell (pi N.det)
  have hc : c ≠ 0 := by
    dsimp [c]
    rw [hell N.det hNdetdeg, hNtop]
    exact hnon
  let d := polynomialDoubleTensorMap P D.det
  obtain ⟨hd, hJac⟩ := polynomial_difference_matrix_diagonal P D hD hder
  change Annihilates (KaehlerDifferential.ideal K Q) d at hd
  have hdc : tensorFunctionalContraction ell d = algebraMap K Q c := by
    have ht := polynomial_double_contraction_constant P B ell hv D.det
      (polynomial_matrix_det_degree D (fun i => e i - 1) hDdeg)
    have hu : u D.det = N.det := u.toRingHom.map_det D
    simpa only [d, c, I, Q, pi, u, hu] using ht
  let ell' := c⁻¹ • ell
  have hscale : tensorFunctionalContraction ell' d = c⁻¹ • tensorFunctionalContraction ell d := by
    induction d using TensorProduct.inductionOn with
    | tmul a b => simp [ell', tensorFunctionalContraction_tmul, smul_smul]
    | add d f hd hf => simp only [map_add, hd, hf, smul_add]
  have hn : tensorFunctionalContraction ell' d = 1 := by
    rw [hscale, hdc, Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  let p := perfectPairingOfNormalizedContraction ell' d hd hn
  have hdiag : pairingDiagonal p = d := normalized_contraction_pairing_diagonal ell' d hd hn
  refine ⟨p, ?_, ?_⟩
  · intro f hf
    change (c⁻¹ • ell) (pi f) = 0
    have hz : ell (pi f) = 0 := hv f hf
    rw [LinearMap.smul_apply, hz, smul_zero]
  · intro a
    change (Algebra.TensorProduct.lmul' K) d =
      Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i))) at hJac
    change p.functional (a * Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i)))) =
      Algebra.trace K Q a
    rw [← hJac, ← hdiag, pairingDiagonal_multiplication_eq_traceElement]
    simpa only [mul_comm] using traceElement_pairing p a

end LinearStudy
