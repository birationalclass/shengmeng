module
public import Linear.ProjectiveGenericFiberRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- On a constructed nonempty target open, the WHOLE original projective
point fiber has cardinality equal to the original pullback's actual
generic rank. Neither a good fiber nor its cardinality is an input.
The q^r rank value and Scheme gluing remain separate obligations. -/
theorem projective_exists_general_whole_fiber_generic_rank
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
    letI : Algebra B A := φ.toRingHom.toAlgebra
    letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
    letI : Module B A := Algebra.toModule
    ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
      (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
      ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        MvPolynomial.eval y p ≠ 0 →
        (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
        (∀ (v : CoordinateVector n) (hv : v ≠ 0),
          f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
        (let ρ := V.affinePointEvaluation y hy
         letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
         Module.Finite ℂ (A ⊗[B] ℂ) ∧ IsReduced (A ⊗[B] ℂ) ∧
           Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) = Module.finrank B A) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
  letI : Module B A := Algebra.toModule
  obtain ⟨p₀, hp₀, _, hgood⟩ :=
    projective_exists_general_whole_reduced_tensor_fibers f V hq hf hV x0 hx0
  obtain ⟨p₁, hp₁, hdim⟩ :=
    projectiveChartOpenMap_exists_generic_rank_fibers f V hq hf hV x0 hx0
  let p := p₀ * p₁
  have hp : p ∉ V.affineIdeal := by
    intro h
    rcases (show V.affineIdeal.IsPrime from inferInstance).mem_or_mem h with h₀ | h₁
    · exact hp₀ h₀
    · exact hp₁ h₁
  obtain ⟨y₀, hy₀, hyp, _⟩ := V.exists_smooth_affine_point_avoiding x0 hx0 p hp
  refine ⟨p, hp, ⟨y₀, hy₀, hyp⟩, ?_⟩
  intro y hy hyp
  have heval : MvPolynomial.eval y p₀ ≠ 0 ∧ MvPolynomial.eval y p₁ ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [p, MvPolynomial.eval_mul] using hyp)
  obtain ⟨hfinite, hchart, hring⟩ := hgood y hy heval.1
  refine ⟨hfinite, hchart, ?_⟩
  dsimp only at hring ⊢
  let ρ := V.affinePointEvaluation y hy
  letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
  obtain ⟨hfin, hred, hcard⟩ := hring
  exact ⟨hfin, hred, hcard.trans (hdim y hy heval.2)⟩

end LinearStudy
