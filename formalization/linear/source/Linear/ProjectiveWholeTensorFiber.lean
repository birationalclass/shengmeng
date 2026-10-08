module
public import Linear.ProjectiveAffineFiberTensor
public import Linear.ProjectiveWholeFiberPointCount
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
variable {n : ℕ}

/-- One COMPLETE original point fiber has a finite reduced actual tensor
fiber ring, with point count equal to the dimension of that tensor ring.
This does not assert that the dimension equals q^r. -/
theorem projective_exists_whole_reduced_tensor_fiber_point_count
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
      (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
      (∀ (v : CoordinateVector n) (hv : v ≠ 0),
        f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
      (let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
       let A := Localization.Away (projectiveChartDenominator f V)
       let φ := projectiveChartOpenMap f V hq hf hV y hy
       let ρ := V.affinePointEvaluation y hy
       letI : Algebra B A := φ.toRingHom.toAlgebra
       letI : SMul B A := (φ.toRingHom.toAlgebra).toSMul
       letI : Module B A := Algebra.toModule
       letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
       Module.Finite ℂ (A ⊗[B] ℂ) ∧ IsReduced (A ⊗[B] ℂ) ∧
         Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
           Module.finrank ℂ (A ⊗[B] ℂ)) := by
  obtain ⟨y, hy, hfiber, hchart, hfinite, hred, hcard⟩ :=
    projective_exists_whole_reduced_fiber_point_count f V hq hf hV x0 hx0
  refine ⟨y, hy, hfiber, hchart, ?_⟩
  dsimp only
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV y hy
  let ρ := V.affinePointEvaluation y hy
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := (φ.toRingHom.toAlgebra).toSMul
  letI : Module B A := Algebra.toModule
  letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
  letI := hfinite
  letI := hred
  obtain ⟨e⟩ := projectiveAffineFiber_exists_tensor_equiv f V hq hf hV y hy
  refine ⟨Module.Finite.equiv e.symm.toLinearEquiv, isReduced_of_injective e e.injective, ?_⟩
  exact hcard.trans e.toLinearEquiv.finrank_eq.symm

end LinearStudy
