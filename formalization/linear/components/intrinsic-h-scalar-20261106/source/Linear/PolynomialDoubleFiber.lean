module
public import Linear.UniversalDifference
public import Linear.PolynomialGlobalResidue
public import Linear.GlobalDiagonalNormalization
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
open scoped TensorProduct
namespace LinearStudy
variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

def polynomialDoubleRightPoint (a : ι → K) :
    MvPolynomial (ι ⊕ ι) K →ₐ[K] MvPolynomial ι K :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (a i)))

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleRightPoint_left (a : ι → K) (P : MvPolynomial ι K) :
    polynomialDoubleRightPoint a (MvPolynomial.rename Sum.inl P) = P := by
  have h : (polynomialDoubleRightPoint a).comp (MvPolynomial.rename Sum.inl) =
      AlgHom.id K (MvPolynomial ι K) := by
    ext i
    simp [polynomialDoubleRightPoint]
  exact DFunLike.congr_fun h P

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleRightPoint_right (a : ι → K) (P : MvPolynomial ι K) :
    polynomialDoubleRightPoint a (MvPolynomial.rename Sum.inr P) =
      MvPolynomial.C (MvPolynomial.eval a P) := by
  have h : (polynomialDoubleRightPoint a).toRingHom.comp (MvPolynomial.rename Sum.inr).toRingHom =
      MvPolynomial.C.comp (MvPolynomial.eval a) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [polynomialDoubleRightPoint]
  exact RingHom.congr_fun h P

theorem polynomial_universal_difference_matrix_general (P : ι → MvPolynomial ι K) :
    ∃ D : Matrix ι ι (MvPolynomial (ι ⊕ ι) K),
      D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
        (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)) ∧
      ∀ i j, polynomialDoubleDiagonal (D i j) = MvPolynomial.pderiv j (P i) := by
  let u : MvPolynomial ι K →+* MvPolynomial (ι ⊕ ι) K :=
    (MvPolynomial.rename Sum.inl).toRingHom
  let v : MvPolynomial ι K →+* MvPolynomial (ι ⊕ ι) K :=
    (MvPolynomial.rename Sum.inr).toRingHom
  let pi := polynomialDoubleDiagonal (R := K) (ι := ι)
  have hc : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c) := by intro c; simp [u, v]
  have hx : ∀ i, pi (u (MvPolynomial.X i)) = pi (v (MvPolynomial.X i)) := by
    intro i; simp [pi, u, v, polynomialDoubleDiagonal]
  choose D hD hd using fun (i : ι) => polynomial_diagonal_difference
    (R := K) (A := MvPolynomial (ι ⊕ ι) K) (B := MvPolynomial ι K) u v pi hc hx (P i)
  let M : Matrix ι ι (MvPolynomial (ι ⊕ ι) K) := D
  refine ⟨M, ?_, ?_⟩
  · funext i
    change (∑ j, D i j * (MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j))) = _
    simpa [u, v] using (hD i).symm
  · intro i j
    exact (hd i j).trans (polynomialDoubleDiagonal_left _)

def polynomialDoubleTensorMap (P : ι → MvPolynomial ι K) :
    MvPolynomial (ι ⊕ ι) K →ₐ[K]
      ((MvPolynomial ι K ⧸ Ideal.span (Set.range P)) ⊗[K]
        (MvPolynomial ι K ⧸ Ideal.span (Set.range P))) :=
  MvPolynomial.aeval (Sum.elim
    (fun i => Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i) ⊗ₜ[K] 1)
    (fun i => 1 ⊗ₜ[K] Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleTensorMap_multiplication
    (P : ι → MvPolynomial ι K) (b : MvPolynomial (ι ⊕ ι) K) :
    Algebra.TensorProduct.lmul' K (polynomialDoubleTensorMap P b) =
      Ideal.Quotient.mk (Ideal.span (Set.range P)) (polynomialDoubleDiagonal b) := by
  have h : (Algebra.TensorProduct.lmul' K).toRingHom.comp (polynomialDoubleTensorMap P).toRingHom =
      (Ideal.Quotient.mk (Ideal.span (Set.range P))).comp polynomialDoubleDiagonal := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensorMap, polynomialDoubleDiagonal]
      rfl
    · intro i
      cases i <;> simp [polynomialDoubleTensorMap, polynomialDoubleDiagonal]
  exact RingHom.congr_fun h b

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleTensorMap_rightReduction
    (P : ι → MvPolynomial ι K)
    (q : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₐ[K] K)
    (b : MvPolynomial (ι ⊕ ι) K) :
    pairingRightReduction q (polynomialDoubleTensorMap P b) =
      Ideal.Quotient.mk (Ideal.span (Set.range P))
        (polynomialDoubleRightPoint
          (fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))) b) := by
  have h : (pairingRightReduction q).toRingHom.comp (polynomialDoubleTensorMap P).toRingHom =
      (Ideal.Quotient.mk (Ideal.span (Set.range P))).comp
        (polynomialDoubleRightPoint (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDoubleTensorMap, polynomialDoubleRightPoint, pairingRightReduction_tmul]
      rfl
    · intro i
      cases i <;> simp [polynomialDoubleTensorMap, polynomialDoubleRightPoint,
        pairingRightReduction_tmul, Algebra.smul_def]
      rfl
  exact RingHom.congr_fun h b

section Field
variable {F : Type*} [Field F]

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleTensorMap_left (P : ι → MvPolynomial ι K) (b : MvPolynomial ι K) :
    polynomialDoubleTensorMap P (MvPolynomial.rename Sum.inl b) =
      Ideal.Quotient.mk (Ideal.span (Set.range P)) b ⊗ₜ[K] 1 := by
  have h : (polynomialDoubleTensorMap P).comp (MvPolynomial.rename Sum.inl) =
      Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ K (Ideal.span (Set.range P))) := by
    ext i
    simp [polynomialDoubleTensorMap]
  exact DFunLike.congr_fun h b

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialDoubleTensorMap_right (P : ι → MvPolynomial ι K) (b : MvPolynomial ι K) :
    polynomialDoubleTensorMap P (MvPolynomial.rename Sum.inr b) =
      1 ⊗ₜ[K] Ideal.Quotient.mk (Ideal.span (Set.range P)) b := by
  have h : (polynomialDoubleTensorMap P).comp (MvPolynomial.rename Sum.inr) =
      Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ K (Ideal.span (Set.range P))) := by
    ext i
    simp [polynomialDoubleTensorMap]
  exact DFunLike.congr_fun h b

theorem polynomial_coefficientDeterminant_ne_zero_at_point {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) F) (List.ofFn P))
    [Module.Finite F (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P))]
    (q : (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)) →ₐ[F] F)
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) F))
    (hN : N.mulVec (fun i => MvPolynomial.X i -
      MvPolynomial.C (q (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))) = P) :
    Ideal.Quotient.mk (Ideal.span (Set.range P)) N.det ≠ 0 := by
  let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
  let a := fun i => q (pi (MvPolynomial.X i))
  let x := fun i => MvPolynomial.X i - MvPolynomial.C (a i)
  have hx := polynomial_centered_variables_regular (n + 1) a
  have hk := polynomial_quotient_coordinateIdeal_eq_kernel P q
  have hmax : ((Ideal.span (Set.range x)).map pi).IsMaximal := by
    change ((Ideal.span (Set.range x)).map pi) = _ at hk
    rw [hk]
    exact RingHom.ker_isMaximal_of_surjective q.toRingHom
      (fun b => ⟨algebraMap F Q b, q.commutes b⟩)
  let : IsNoetherianRing Q := IsNoetherianRing.of_finite F Q
  let : IsArtinianRing Q := IsArtinianRing.of_finite F Q
  exact coefficientDeterminant_ne_zero_of_artinian_maximal P x hP hx N hN hmax

theorem polynomial_universal_determinant_rightReduction_ne_zero {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) F) (List.ofFn P))
    [Module.Finite F (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P))]
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) F))
    (hD : D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
      (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)))
    (q : (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)) →ₐ[F] F) :
    pairingRightReduction q (polynomialDoubleTensorMap P D.det) ≠ 0 := by
  let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mkₐ F (Ideal.span (Set.range P))
  let a := fun i => q (pi (MvPolynomial.X i))
  let e := polynomialDoubleRightPoint a
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) F) :=
    fun i j => e (D i j)
  have he : q.comp pi = MvPolynomial.aeval (R := F) a := by ext i; simp [a]
  have hp0 (i : Fin (n + 1)) : MvPolynomial.eval a (P i) = 0 := by
    change MvPolynomial.aeval (R := F) a (P i) = 0
    rw [← he]
    change q (pi (P i)) = 0
    have hp : pi (P i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    rw [hp, map_zero]
  have hN : N.mulVec (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) = P := by
    funext i
    have hh := congrArg e (congrFun hD i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub] at hh
    simp only [e, polynomialDoubleRightPoint_left, polynomialDoubleRightPoint_right,
      hp0, map_zero, sub_zero] at hh
    simpa [N, e, Matrix.mulVec, dotProduct, polynomialDoubleRightPoint] using hh
  have hn := polynomial_coefficientDeterminant_ne_zero_at_point P hP q N hN
  rw [polynomialDoubleTensorMap_rightReduction]
  have hd : e D.det = N.det := e.toRingHom.map_det D
  exact hd ▸ hn

theorem polynomialQuotient_nondegenerate_diagonal {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) F) (List.ofFn P))
    [Module.Finite F (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P))] :
    let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    ∃ d : Q ⊗[F] Q, Annihilates (KaehlerDifferential.ideal F Q) d ∧
      Algebra.TensorProduct.lmul' F d = Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i))) ∧
      ∀ q : Q →ₐ[F] F, pairingRightReduction q d ≠ 0 := by
  classical
  let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mkₐ F (Ideal.span (Set.range P))
  obtain ⟨D, hD, hd⟩ := polynomial_universal_difference_matrix_general P
  let phi := polynomialDoubleTensorMap P
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Q ⊗[F] Q) := fun i j => phi (D i j)
  have he : M.mulVec (fun i => pi (MvPolynomial.X i) ⊗ₜ[F] (1 : Q) -
      (1 : Q) ⊗ₜ[F] pi (MvPolynomial.X i)) = 0 := by
    funext i
    have hh := congrArg phi (congrFun hD i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_sub] at hh
    have hp : pi (P i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
    simp only [phi, polynomialDoubleTensorMap_left, polynomialDoubleTensorMap_right] at hh
    change (∑ j, polynomialDoubleTensorMap P (D i j) *
      (polynomialDoubleTensorMap P (MvPolynomial.X (Sum.inl j)) -
        polynomialDoubleTensorMap P (MvPolynomial.X (Sum.inr j)))) =
      pi (P i) ⊗ₜ[F] (1 : Q) - (1 : Q) ⊗ₜ[F] pi (P i) at hh
    rw [hp] at hh
    simpa [M, phi, pi, Matrix.mulVec, dotProduct, polynomialDoubleTensorMap] using hh
  have hm : phi D.det = M.det := by
    change (polynomialDoubleTensorMap P).toRingHom D.det =
      ((polynomialDoubleTensorMap P).toRingHom.mapMatrix D).det
    exact RingHom.map_det (S := Q ⊗[F] Q) (polynomialDoubleTensorMap P).toRingHom D
  refine ⟨M.det, ?_, ?_, ?_⟩
  · rw [← polynomial_tensor_diagonal_eq_coordinate_ideal pi Ideal.Quotient.mk_surjective]
    exact determinant_annihilates_coordinate_ideal M _ he
  · rw [← hm, polynomialDoubleTensorMap_multiplication]
    calc
      Ideal.Quotient.mk (Ideal.span (Set.range P)) (polynomialDoubleDiagonal D.det) =
        Matrix.det (fun i j => Ideal.Quotient.mk (Ideal.span (Set.range P)) (polynomialDoubleDiagonal (D i j))) := by
          rw [RingHom.map_det polynomialDoubleDiagonal D,
            RingHom.map_det (Ideal.Quotient.mk (Ideal.span (Set.range P)))]
          rfl
      _ = Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i))) := by
        congr 1
        funext i j
        rw [hd i j]
        rfl
  · intro q
    rw [← hm]
    exact polynomial_universal_determinant_rightReduction_ne_zero P hP D hD q

theorem polynomialQuotient_normalized_trace [IsAlgClosed F] [Infinite F] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) F) (List.ofFn P))
    [Module.Finite F (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P))] :
    let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    ∃ p : PerfectMultiplicationPairing (B := F) (A := Q), ∀ a : Q,
      p.functional (a * Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i)))) =
        Algebra.trace F Q a := by
  let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
  obtain ⟨p⟩ := polynomialQuotient_perfectPairing P hP
  obtain ⟨d, hd, hj, hred⟩ := polynomialQuotient_nondegenerate_diagonal P hP
  choose q hq using fun j : MaximalSpectrum Q => exists_maximalResidueMap (K := F) j
  obtain ⟨p', _, ht⟩ := global_diagonal_normalized_trace q hq p d hd (fun j => hred (q j))
  refine ⟨p', ?_⟩
  intro a
  rw [← hj]
  exact ht a

theorem polynomialQuotient_diagonal_unique_functional [IsAlgClosed F] [Infinite F] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F)
    (hP : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) F) (List.ofFn P))
    [Module.Finite F (MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P))] :
    let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    ∃ d : Q ⊗[F] Q, Annihilates (KaehlerDifferential.ideal F Q) d ∧
      Algebra.TensorProduct.lmul' F d = Matrix.det (fun i j => pi (MvPolynomial.pderiv j (P i))) ∧
      ∃! ell : Q →ₗ[F] F, tensorFunctionalContraction ell d = 1 := by
  let Q := MvPolynomial (Fin (n + 1)) F ⧸ Ideal.span (Set.range P)
  obtain ⟨p⟩ := polynomialQuotient_perfectPairing P hP
  obtain ⟨d, hd, hj, hred⟩ := polynomialQuotient_nondegenerate_diagonal P hP
  choose q hq using fun j : MaximalSpectrum Q => exists_maximalResidueMap (K := F) j
  exact ⟨d, hd, hj, global_diagonal_unique_functional q hq p d hd (fun j => hred (q j))⟩
end Field

end LinearStudy
