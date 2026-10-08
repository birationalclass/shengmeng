module
public import Linear.ProjectivePullbackComposition
public import Linear.FieldEndomorphismDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem HomogeneousEndomorphism.iterate_degree_pos
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (k : ℕ) :
    0 < (f.iterate k).degree := by
  rw [f.iterate_degree]
  exact pow_pos hq k

theorem HomogeneousEndomorphism.iterate_surjective
    (f : HomogeneousEndomorphism n) (hf : Function.Surjective f.onPoints) (k : ℕ) :
    Function.Surjective (f.iterate k).onPoints := by
  rw [f.iterate_onPoints]
  exact hf.iterate k

theorem projectiveCoordinateFractionMap_identity
    (V : IntegralProjectiveEquations n)
    (hq : 0 < (HomogeneousEndomorphism.identity n).degree)
    (hf : Function.Surjective (HomogeneousEndomorphism.identity n).onPoints)
    (hV : (HomogeneousEndomorphism.identity n).onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    projectiveCoordinateFractionMap (HomogeneousEndomorphism.identity n) V hq hf hV = 1 := by
  letI := V.prime
  have hpoly : (MvPolynomial.aeval (HomogeneousEndomorphism.identity n).forms :
      CoordinateRing n →ₐ[ℂ] CoordinateRing n) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  have hd : projectiveCoordinateDomainMap (HomogeneousEndomorphism.identity n) V hq hf hV =
      AlgHom.id ℂ _ := by
    apply AlgHom.ext
    intro a
    obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [projectiveCoordinateDomainMap_mk, hpoly]
    rfl
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordinateRing n ⧸ V.ideal.toIdeal))
  apply RingHom.ext
  intro a
  change projectiveCoordinateFractionMap (HomogeneousEndomorphism.identity n) V hq hf hV
      (algebraMap _ (FractionRing _) a) = algebraMap _ (FractionRing _) a
  rw [projectiveCoordinateFractionMap_algebraMap, hd]
  rfl

theorem projectiveChartFractionMap_identity
    (V : IntegralProjectiveEquations n)
    (hq : 0 < (HomogeneousEndomorphism.identity n).degree)
    (hf : Function.Surjective (HomogeneousEndomorphism.identity n).onPoints)
    (hV : (HomogeneousEndomorphism.identity n).onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    projectiveChartFractionMap (HomogeneousEndomorphism.identity n) V hq hf hV x0 hx0 = 1 := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  apply AlgHom.ext
  intro z
  apply (projectiveChartFractionEmbedding V x0 hx0).injective
  change projectiveChartFractionEmbedding V x0 hx0
      (projectiveChartFractionMap (HomogeneousEndomorphism.identity n) V hq hf hV x0 hx0 z) =
    projectiveChartFractionEmbedding V x0 hx0 z
  rw [projectiveChartFractionMap_commutes, projectiveCoordinateFractionMap_identity]
  rfl

/-- The ORIGINAL iterated projective map induces precisely the power
of the ORIGINAL function-field pullback in the same fraction model. -/
theorem projectiveChartFractionMap_iterate
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) (k : ℕ) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    projectiveChartFractionMap (f.iterate k) V (f.iterate_degree_pos hq k)
      (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0 =
        (projectiveChartFractionMap f V hq hf hV x0 hx0) ^ k := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  induction k with
  | zero =>
    rw [pow_zero]
    exact projectiveChartFractionMap_identity V
      (f.iterate_degree_pos hq 0) (f.iterate_surjective hf 0)
      (f.iterate_total_invariance V.zeroSet hV 0) x0 hx0
  | succ k ih =>
    have hc := projectiveChartFractionMap_comp f (f.iterate k) V hq
      (f.iterate_degree_pos hq k) hf (f.iterate_surjective hf k) hV
      (f.iterate_total_invariance V.zeroSet hV k)
      (f.iterate_degree_pos hq (k+1)) (f.iterate_surjective hf (k+1))
      (f.iterate_total_invariance V.zeroSet hV (k+1)) x0 hx0
    exact hc.trans (by rw [ih, pow_succ]; rfl)

/-- Its actual function-field degree, with no input degree value. -/
theorem projectiveChartFractionMap_iterate_finrank
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) (k : ℕ) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
    let γk := projectiveChartFractionMap (f.iterate k) V (f.iterate_degree_pos hq k)
      (f.iterate_surjective hf k) (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
    Module.finrank γk.fieldRange (FractionRing B) =
      (Module.finrank γ.fieldRange (FractionRing B)) ^ k := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  dsimp only
  rw [projectiveChartFractionMap_iterate]
  exact fieldEndomorphism_finrank_pow _ k

end LinearStudy
