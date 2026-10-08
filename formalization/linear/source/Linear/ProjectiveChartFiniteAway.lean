module
public import Linear.AlgebraicFiniteTypeAway
public import Linear.ProjectiveTargetGoodOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL rational chart pullback becomes module-finite over a
nonempty target principal open, without an assumed finite-map witness. -/
theorem projectiveChartOpenMap_exists_finite_target_away
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x hx
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ b : B, b ≠ 0 ∧
      (let R := Localization.Away b
       let S := Localization.Away (algebraMap B A b)
       let ψ := Localization.awayMapₐ (Algebra.ofId B A) b
       letI : Algebra R S := ψ.toRingHom.toAlgebra
       Module.Finite R S) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : Algebra.FiniteType B A := projectiveChartOpenMap_finiteType f V hq hf hV x hx
  letI : Algebra.IsAlgebraic B A := projectiveChartOpenMap_isAlgebraic f V hq hf hV x hx
  obtain ⟨b, hb, hfin⟩ := algebraic_finiteType_exists_finite_away (R := B) (S := A)
  exact ⟨b, hb, hfin⟩

end LinearStudy
