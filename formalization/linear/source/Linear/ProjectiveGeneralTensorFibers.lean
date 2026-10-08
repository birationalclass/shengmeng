module
public import Linear.ProjectiveGeneralReducedFibers
public import Linear.ProjectiveAffineFiberTensor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
variable {n : ℕ}

/-- Every whole fiber over a constructed nonempty target principal open is
finite and has a reduced actual tensor fiber ring. Its point count equals
the tensor ring's dimension; the q^r value is a separate obligation. -/
theorem projective_exists_general_whole_reduced_tensor_fibers
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
      (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
      ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        MvPolynomial.eval y p ≠ 0 →
        (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
        (∀ (v : CoordinateVector n) (hv : v ≠ 0),
          f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
        (let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
         let A := Localization.Away (projectiveChartDenominator f V)
         let φ := projectiveChartOpenMap f V hq hf hV y hy
         let ρ := V.affinePointEvaluation y hy
         letI : Algebra B A := φ.toRingHom.toAlgebra
         letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
         letI : Module B A := Algebra.toModule
         letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
         Module.Finite ℂ (A ⊗[B] ℂ) ∧ IsReduced (A ⊗[B] ℂ) ∧
           Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
             Module.finrank ℂ (A ⊗[B] ℂ)) := by
  obtain ⟨p, hp, _, hnonempty, hgood⟩ :=
    projective_exists_general_whole_reduced_fibers f V hq hf hV x0 hx0
  refine ⟨p, hp, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hfiber, hchart, hfinite, hred, hcard⟩ := hgood y hy hyp
  refine ⟨hfiber, hchart, ?_⟩
  dsimp only
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV y hy
  let ρ := V.affinePointEvaluation y hy
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
  letI : Module B A := Algebra.toModule
  letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
  letI := hfinite
  letI := hred
  obtain ⟨e⟩ := projectiveAffineFiber_exists_tensor_equiv f V hq hf hV y hy
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
    isReduced_of_injective e e.injective,
    hcard.trans e.toLinearEquiv.finrank_eq.symm⟩

end LinearStudy
