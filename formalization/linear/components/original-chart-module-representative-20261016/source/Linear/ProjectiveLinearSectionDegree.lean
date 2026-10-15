module
public import Linear.PolynomialTotalDegreeHilbert
public import Linear.PolynomialGrowthLeadingCoeff
public import Linear.HilbertLeadingCoeffCumulative
public import Linear.LinearProjectionFilteredGrowth
public import Linear.ProjectiveGenericGrowthDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open Filter
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra

/-- From the original V alone, generic linear sections have cardinality equal
to its factorial-normalized Hilbert leading coefficient. The SAME actual
projection supplies both point counts and the growth comparison proving the
degree formula; rank is not renamed as degree to bypass the comparison. -/
theorem projective_exists_linear_section_hilbert_degree {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := V.prime
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      (∃ N : ℕ, ∀ j > N, P.eval (j : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal j : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        let R := MvPolynomial (Fin (r+1)) ℂ
        let A := CoordinateRing n ⧸ V.ideal.toIdeal
        let φ := projectiveLinearNormalizationMap V L
        letI : Algebra R A := φ.toRingHom.toAlgebra
        letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
        letI : Module R A := Algebra.toModule
        ∃ (d : ℕ) (c : R), 0 < d ∧ d = Module.finrank R A ∧
          (d : ℚ) = (r.factorial : ℚ) * P.leadingCoeff ∧ c ≠ 0 ∧
          (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
          ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
            w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w) = d := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,m,B,E,c,hm,hc,hex,hsect,hgrowth⟩ :=
    projective_exists_same_linear_section_generic_growth V
  obtain ⟨C,hC,hCdegree,hClc,NC,hNC⟩ :=
    homogeneousQuotientCumulativeHilbertPolynomial_normalized_leadingCoeff
      V.ideal.toIdeal V.ideal.isHomogeneous P hP hHilbert
  let S := Polynomial.preHilbertPoly ℚ (r+1) 0
  have hS : S ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero]
    simp [S,Polynomial.leadingCoeff_preHilbertPoly,Nat.factorial_ne_zero]
  have hSCdegree : C.natDegree=S.natDegree := by
    simpa [S,hdegree,Polynomial.natDegree_preHilbertPoly] using hCdegree
  have hSpos : ∀ᶠ N : ℕ in atTop, 0 < S.eval (N : ℚ) := by
    apply Filter.Eventually.of_forall
    intro N
    rw [show S.eval (N : ℚ)=((N+(r+1)).choose (r+1) : ℚ) by
      simpa [S] using Polynomial.preHilbertPoly_eq_choose_add_sub ℚ (r+1)
        (k:=0) (n:=N) (Nat.zero_le _)]
    exact_mod_cast Nat.choose_pos (show r+1 ≤ N+(r+1) by omega)
  have hClcRank : C.leadingCoeff=(m : ℚ)*S.leadingCoeff := by
    apply polynomial_two_sided_growth_leadingCoeff S C hS hC hSCdegree m B E hSpos
    · filter_upwards [eventually_gt_atTop NC] with N hn
      have he : C.eval ((N : ℚ)+B)=
          (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (N+B)) : ℚ) := by
        simpa only [Nat.cast_add] using hNC (N+B) (by omega)
      rw [he,show S.eval (N : ℚ)=
        (Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin (r+1)) ℂ N) : ℚ)
        from polynomial_restrictTotalDegree_hilbert_eval ℂ (r+1) N]
      exact_mod_cast (hgrowth N).1
    · filter_upwards [eventually_gt_atTop NC] with N hn
      have he : S.eval ((N : ℚ)+E)=
          (Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin (r+1)) ℂ (N+E)) : ℚ) := by
        simpa only [Nat.cast_add] using
          polynomial_restrictTotalDegree_hilbert_eval ℂ (r+1) (N+E)
      rw [hNC N hn,he]
      exact_mod_cast (hgrowth N).2
  have hCdeg : C.natDegree=r+1 := hCdegree.trans (congrArg (fun j => j+1) hdegree)
  have hdegreeFormula : (m : ℚ)=(r.factorial : ℚ)*P.leadingCoeff := by
    have h := hClc
    rw [hCdeg,hdegree,hClcRank,show S.leadingCoeff=((r+1).factorial : ℚ)⁻¹ by
      simp [S,Polynomial.leadingCoeff_preHilbertPoly]] at h
    have hnf : ((r+1).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (r+1)
    field_simp at h
    exact h
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m=0 := Nat.eq_zero_of_not_pos h
    have h0 : Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal 0) ≤ 0 := by
      simpa [hm0] using (hgrowth 0).2
    exact (not_lt_of_ge h0) (projective_coordinate_filtration_finrank_pos V 0)
  exact ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,m,c,hmpos,hm,hdegreeFormula,hc,hex,hsect⟩

end LinearStudy
