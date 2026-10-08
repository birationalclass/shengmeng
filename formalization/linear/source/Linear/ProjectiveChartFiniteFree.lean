module
public import Linear.ProjectiveChartFiniteAway
public import Linear.GenericFreeAway
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Construct finite and then free target opens for the SAME original
chart pullback. The rank is that of the actual localized module; it is
not assumed to be q^r. The second localization is a module localization. -/
theorem projectiveChartOpenMap_exists_finite_free_target_opens
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x hx
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ (b : B), b ≠ 0 ∧
      (let R := Localization.Away b
       let S := Localization.Away (algebraMap B A b)
       let ψ := Localization.awayMapₐ (Algebra.ofId B A) b
       letI : Algebra R S := ψ.toRingHom.toAlgebra
       letI : SMul R S := ψ.toRingHom.toAlgebra.toSMul
       letI : Module R S := Algebra.toModule
       Module.Finite R S ∧
         ∃ c : R, c ≠ 0 ∧
           Module.Free (Localization.Away c) (LocalizedModule.Away c S) ∧
           Module.finrank (Localization.Away c) (LocalizedModule.Away c S) =
             Module.finrank R S) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨b, hb, hfin⟩ := projectiveChartOpenMap_exists_finite_target_away f V hq hf hV x hx
  refine ⟨b, hb, ?_⟩
  dsimp only
  let R := Localization.Away b
  let S := Localization.Away (algebraMap B A b)
  let ψ := Localization.awayMapₐ (Algebra.ofId B A) b
  letI : Algebra R S := ψ.toRingHom.toAlgebra
  letI : SMul R S := ψ.toRingHom.toAlgebra.toSMul
  letI : Module R S := Algebra.toModule
  letI : IsDomain R := Localization.Away.isDomain hb
  letI : Module.Finite R S := hfin
  exact ⟨hfin, finiteModule_exists_free_away⟩

end LinearStudy
