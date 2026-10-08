module
public import Linear.AlgebraicGenericFiberRank
public import Linear.ProjectiveGeneralTensorFibers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The original chart pullback has its actual generic rank at every
field-valued fiber over a constructed nonempty target open. Its rank
value is not supplied or computed as q^r. -/
theorem projectiveChartOpenMap_exists_generic_rank_fibers
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
      ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        MvPolynomial.eval y p ≠ 0 →
        (let ρ := V.affinePointEvaluation y hy
         letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
         Module.finrank ℂ (A ⊗[B] ℂ) = Module.finrank B A) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
  letI : Module B A := Algebra.toModule
  letI : Algebra.FiniteType B A := projectiveChartOpenMap_finiteType f V hq hf hV x0 hx0
  letI : Algebra.IsAlgebraic B A := projectiveChartOpenMap_isAlgebraic f V hq hf hV x0 hx0
  obtain ⟨b, hb, hdim⟩ := algebraic_finiteType_exists_generic_rank_fibers
    (R := B) (A := A) (K := ℂ)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective b
  have hpI : p ∉ V.affineIdeal := by
    intro h
    exact hb (hp.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  refine ⟨p, hpI, ?_⟩
  intro y hy hyp
  dsimp only
  let ρ := V.affinePointEvaluation y hy
  letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ B A := IsScalarTower.of_algHom φ
  letI : IsScalarTower ℂ B ℂ := IsScalarTower.of_algHom ρ
  have hρb : ρ b ≠ 0 := by
    rw [← hp, V.affinePointEvaluation_mk]
    exact hyp
  have hd := hdim ρ.toRingHom hρb
  let e : (A ⊗[B] ℂ) ≃ₗ[ℂ] ℂ ⊗[B] A :=
    (TensorProduct.comm B A ℂ).restrictScalars ℂ
  exact e.finrank_eq.trans hd

end LinearStudy
