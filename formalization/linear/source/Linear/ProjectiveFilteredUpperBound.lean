module
public import Linear.ProjectiveFilteredCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n m : ℕ}

/-- The ACTUAL coordinate filtration has an upper growth bound obtained
from the constructed generic family and a common denominator. Neither
growth comparisons nor a degree formula are hypotheses. -/
theorem projectiveCoordinateFiltration_generic_upper
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (b : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal) (d : Fin m → ℕ)
    (hb : ∀ i, b i ∈ homogeneousQuotientPiece V.ideal.toIdeal (d i))
    (hli : let A := CoordinateRing n ⧸ V.ideal.toIdeal
      let φ := projectiveCoordinateDomainMap f V hq hf hV
      letI : Algebra A A := φ.toRingHom.toAlgebra
      letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
      letI : Module A A := Algebra.toModule
      LinearIndependent A b)
    (r : CoordinateRing n ⧸ V.ideal.toIdeal) (hr : r ≠ 0) (R : ℕ)
    (hrR : r ∈ homogeneousQuotientFiltration V.ideal.toIdeal R)
    (hden : ∀ x : CoordinateRing n ⧸ V.ideal.toIdeal,
      ∃ c : Fin m → CoordinateRing n ⧸ V.ideal.toIdeal,
        (∑ i, projectiveCoordinateDomainMap f V hq hf hV (c i) * b i) =
          projectiveCoordinateDomainMap f V hq hf hV r * x)
    (N : ℕ) :
    Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
      m * Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal
        ((f.degree * R + N) / f.degree)) := by
  classical
  letI := V.prime
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  let M := (f.degree * R + N) / f.degree
  letI := homogeneousQuotientFiltration_finite V.ideal.toIdeal N
  letI := homogeneousQuotientFiltration_finite V.ideal.toIdeal M
  let L := projectiveFilteredCombination f V hq hf hV b M
  let μ : homogeneousQuotientFiltration V.ideal.toIdeal N →ₗ[ℂ] A :=
    { toFun x := φ r * x
      map_add' x y := by simp [mul_add]
      map_smul' a x := by simp [mul_smul_comm] }
  have hmem : ∀ x : homogeneousQuotientFiltration V.ideal.toIdeal N, μ x ∈ L.range := by
    intro x
    obtain ⟨c, hc⟩ := hden x
    have hbound : (∑ i, φ (c i) * b i) ∈
        homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * R + N) := by
      rw [hc]
      exact homogeneousQuotientFiltration_mul_mem V.ideal.toIdeal _ _ _ _
        (projectiveCoordinateDomainMap_filtration_mem f V hq hf hV R r hrR) x.property
    have hcb := projectiveCoordinateCombination_coefficients_bounded
      f V hq hf hV b c d hb hli (f.degree * R + N) hbound
    refine ⟨fun i => ⟨c i, hcb i⟩, ?_⟩
    exact hc
  let U := μ.codRestrict L.range hmem
  have hφr : φ r ≠ 0 := by
    intro heq
    exact hr (projectiveCoordinateDomainMap_injective f V hq hf hV
      (heq.trans (map_zero φ).symm))
  have hU : Function.Injective U := by
    intro x y heq
    have heq' := congrArg Subtype.val heq
    change φ r * (x : A) = φ r * (y : A) at heq'
    exact Subtype.ext (mul_left_cancel₀ hφr heq')
  have h1 := LinearMap.finrank_le_finrank_of_injective hU
  have h2 := LinearMap.finrank_range_le L
  have h := h1.trans h2
  simpa [Module.finrank_pi_fintype, M] using h

end LinearStudy
