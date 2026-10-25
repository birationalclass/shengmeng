module
public import Linear.LinearProjectionGradedControl
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type*} [Field K] {m : ℕ}

def linearProjectionFilteredCombination
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K)
    (b : Fin m → MvPolynomial σ K ⧸ I) (N : ℕ) :
    (Fin m → MvPolynomial.restrictTotalDegree τ K N) →ₗ[K] (MvPolynomial σ K ⧸ I) where
  toFun c := ∑ i, ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)) (c i) * b i
  map_add' c e := by simp [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' a c := by simp [map_smul,smul_mul_assoc,Finset.smul_sum]

theorem linearProjectionFilteredCombination_degree_bound
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (b : Fin m → MvPolynomial σ K ⧸ I) (N B : ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientFiltration I B)
    (c : Fin m → MvPolynomial.restrictTotalDegree τ K N) :
    linearProjectionFilteredCombination I L b N c ∈ homogeneousQuotientFiltration I (N+B) := by
  change (∑ i, ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)) (c i) * b i) ∈ _
  apply Submodule.sum_mem
  intro i hi
  exact homogeneousQuotientFiltration_mul_mem I _ _ _ _
    (linear_projection_filtration_mem I hI L hL N (c i)
      ((MvPolynomial.mem_restrictTotalDegree τ N _).mp (c i).property)) (hb i)

theorem linearProjectionFilteredCombination_injective
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K)
    (b : Fin m → MvPolynomial σ K ⧸ I)
    (hli : let R := MvPolynomial τ K
      let A := MvPolynomial σ K ⧸ I
      let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
      letI : Algebra R A := φ.toRingHom.toAlgebra
      letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
      letI : Module R A := Algebra.toModule
      LinearIndependent R b) (N : ℕ) :
    Function.Injective (linearProjectionFilteredCombination I L b N) := by
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  intro c e heq
  have heq' : (∑ i,(c i : R) • b i) = ∑ i,(e i : R) • b i := heq
  funext i
  exact Subtype.ext (hli.eq_coords_of_eq heq' i)

theorem linearProjectionFilteredCombination_finrank_lower [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (b : Fin m → MvPolynomial σ K ⧸ I)
    (hli : let R := MvPolynomial τ K
      let A := MvPolynomial σ K ⧸ I
      let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
      letI : Algebra R A := φ.toRingHom.toAlgebra
      letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
      letI : Module R A := Algebra.toModule
      LinearIndependent R b) (N B : ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientFiltration I B) :
    m * Module.finrank K (MvPolynomial.restrictTotalDegree τ K N) ≤
      Module.finrank K (homogeneousQuotientFiltration I (N+B)) := by
  letI := homogeneousQuotientFiltration_finite I (N+B)
  let T := (linearProjectionFilteredCombination I L b N).codRestrict
    (homogeneousQuotientFiltration I (N+B))
    (linearProjectionFilteredCombination_degree_bound I hI L hL b N B hb)
  have hT : Function.Injective T := by
    intro c e h
    exact linearProjectionFilteredCombination_injective I L b hli N (congrArg Subtype.val h)
  simpa [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hT

/-- Both growth bounds retain the ACTUAL generic rank. The generic
family and denominator come from the finite linear projection itself.
No Hilbert coefficient/rank equality is assumed. -/
theorem linear_projection_exists_generic_growth_comparison [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) (hprime : I.IsPrime)
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ _))
    (L : τ → MvPolynomial σ K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)))
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)).Finite) :
    let R := MvPolynomial τ K
    let A := MvPolynomial σ K ⧸ I
    let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
    letI : Module R A := Algebra.toModule
    ∃ (m B E : ℕ), m = Module.finrank R A ∧ ∀ N : ℕ,
      (m * Module.finrank K (MvPolynomial.restrictTotalDegree τ K N) ≤
        Module.finrank K (homogeneousQuotientFiltration I (N+B))) ∧
      (Module.finrank K (homogeneousQuotientFiltration I N) ≤
        m * Module.finrank K (MvPolynomial.restrictTotalDegree τ K (N+E))) := by
  classical
  letI := hprime
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  obtain ⟨m,b,s,hm,hhom,hli,hs,hden⟩ :=
    finite_coordinate_map_exists_generic_homogeneous_control I hI φ hfinite
  choose d hd using hhom
  let B := Finset.univ.sup d
  have hbB : ∀ i, b i ∈ homogeneousQuotientFiltration I B := by
    intro i
    exact Finset.le_sup (f := homogeneousQuotientPiece I)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)))) (hd i)
  refine ⟨m,B,s.totalDegree,hm,?_⟩
  intro N
  refine ⟨linearProjectionFilteredCombination_finrank_lower I hI L hL b hli N B hbB,?_⟩
  let M := N+s.totalDegree
  letI := homogeneousQuotientFiltration_finite I N
  let T := linearProjectionFilteredCombination I L b M
  let μ : homogeneousQuotientFiltration I N →ₗ[K] A :=
    { toFun x := φ s * x
      map_add' x y := by simp [mul_add]
      map_smul' a x := by simp [mul_smul_comm] }
  have hmem : ∀ x : homogeneousQuotientFiltration I N, μ x ∈ T.range := by
    intro x
    obtain ⟨c,hc⟩ := hden x
    have hbound : (∑ i,φ (c i)*b i) ∈ homogeneousQuotientFiltration I M := by
      rw [hc]
      dsimp [M]
      rw [Nat.add_comm]
      exact homogeneousQuotientFiltration_mul_mem I _ _ _ _
        (linear_projection_filtration_mem I hI L hL s.totalDegree s le_rfl) x.property
    have hcb := linear_projection_combination_coefficients_bounded I hI L hL b d hd hli c M hbound
    refine ⟨fun i => ⟨c i,(MvPolynomial.mem_restrictTotalDegree τ M _).mpr (hcb i)⟩,hc⟩
  let U := μ.codRestrict T.range hmem
  have hφs : φ s ≠ 0 := fun h => hs (hinj (h.trans (map_zero φ).symm))
  have hU : Function.Injective U := by
    intro x y h
    have he := congrArg Subtype.val h
    change φ s * (x : A) = φ s * (y : A) at he
    exact Subtype.ext (mul_left_cancel₀ hφs he)
  have h := (LinearMap.finrank_le_finrank_of_injective hU).trans (LinearMap.finrank_range_le T)
  simpa [Module.finrank_pi_fintype,M] using h

/-- One and the SAME original linear projection now controls actual
section point counts and both Hilbert growth bounds. Neither a rank
formula nor a section cardinality is a supplied hypothesis. -/
theorem projective_exists_same_linear_section_generic_growth {n : ℕ}
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
        ∃ (m B E : ℕ) (c : R), m = Module.finrank R A ∧ c ≠ 0 ∧
          (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
          (∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
            w 0 ≠ 0 ∧ Nat.card (projectiveLinearSection V L w) = m) ∧
          ∀ N : ℕ,
            (m * Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin (r+1)) ℂ N) ≤
              Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (N+B))) ∧
            (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
              m * Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin (r+1)) ℂ (N+E))) := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,c,hc,hex,hsect⟩ :=
    projective_exists_linear_projection_section_card V
  obtain ⟨m,B,E,hm,hgrowth⟩ := linear_projection_exists_generic_growth_comparison
    V.ideal.toIdeal V.prime V.ideal.isHomogeneous L hL hinj hfinite
  refine ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,m,B,E,c,hm,hc,hex,?_,hgrowth⟩
  intro w hw
  obtain ⟨hw0,hcard⟩ := hsect w hw
  exact ⟨hw0,hcard.trans hm.symm⟩

end LinearStudy
