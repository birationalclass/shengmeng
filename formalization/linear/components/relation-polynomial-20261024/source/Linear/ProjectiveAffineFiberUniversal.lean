module
public import Linear.ProjectiveAffineFiberMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- The actual polynomial fiber-equation quotient has the universal property
of the original pullback specialized at the specified target point. -/
theorem projectiveAffineFiberChartMap_exists_unique_lift
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    {C : Type*} [CommRing C] [Algebra ℂ C]
    (χ : Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] C)
    (hχ : χ.comp (projectiveChartOpenMap f V hq hf hV y hy) =
      (Algebra.ofId ℂ C).comp (V.affinePointEvaluation y hy)) :
    ∃! ψ : (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) →ₐ[ℂ] C,
      ψ.comp (projectiveAffineFiberChartMap f V y) = χ := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let I := projectiveAffineFiberIdeal f V y
  let η : MvPolynomial (Fin n) ℂ →ₐ[ℂ] C :=
    χ.comp ((IsScalarTower.toAlgHom ℂ B A).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal))
  have hinv : η (affineChartPolynomialMap (f.forms 0)) *
      χ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) = 1 := by
    change χ (algebraMap B A (projectiveChartDenominator f V)) *
      χ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) = 1
    have h := congrArg χ (IsLocalization.Away.mul_invSelf (projectiveChartDenominator f V)
      (S := A))
    simpa only [map_mul, map_one] using h
  have hcoord (i : Fin n) :
      η (affineChartPolynomialMap (f.forms i.succ)) *
        χ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) = algebraMap ℂ C (y i) := by
    have h := AlgHom.congr_fun hχ (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))
    change χ (projectiveChartOpenMap f V hq hf hV y hy
      (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) =
        algebraMap ℂ C (V.affinePointEvaluation y hy
          (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) at h
    rw [projectiveChartOpenMap_mk, V.affinePointEvaluation_mk] at h
    simp only [projectiveChartOpenPolynomialMap, MvPolynomial.aeval_X,
      MvPolynomial.eval_X, map_mul] at h
    exact h
  have hrel (i : Fin n) :
      η (affineChartPolynomialMap (f.forms i.succ)) =
        algebraMap ℂ C (y i) * η (affineChartPolynomialMap (f.forms 0)) := by
    calc
      η (affineChartPolynomialMap (f.forms i.succ)) =
          η (affineChartPolynomialMap (f.forms i.succ)) *
            (η (affineChartPolynomialMap (f.forms 0)) *
              χ (IsLocalization.Away.invSelf (projectiveChartDenominator f V))) := by rw [hinv, mul_one]
      _ = (η (affineChartPolynomialMap (f.forms i.succ)) *
            χ (IsLocalization.Away.invSelf (projectiveChartDenominator f V))) *
              η (affineChartPolynomialMap (f.forms 0)) := by ring
      _ = _ := by rw [hcoord]
  have hI : ∀ p ∈ I, η p = 0 := by
    have hle : I ≤ RingHom.ker η.toRingHom := by
      apply sup_le
      · intro p hp
        change χ (algebraMap B A (Ideal.Quotient.mk V.affineIdeal p)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
      · apply Ideal.span_le.mpr
        rintro p ⟨i, rfl⟩
        change η _ = 0
        rw [map_sub, map_mul, MvPolynomial.algHom_C, hrel, sub_self]
    intro p hp
    exact RingHom.mem_ker.mp (hle hp)
  let ψ := Ideal.Quotient.liftₐ I η hI
  have hψ : ψ.comp (projectiveAffineFiberChartMap f V y) = χ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (projectiveChartDenominator f V))
    apply AlgHom.ext
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    change ψ (projectiveAffineFiberChartMap f V y (algebraMap B A
      (Ideal.Quotient.mk V.affineIdeal p))) = χ (algebraMap B A
        (Ideal.Quotient.mk V.affineIdeal p))
    rw [projectiveAffineFiberChartMap_algebraMap]
    exact Ideal.Quotient.lift_mk _ _ _
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply AlgHom.ext
  intro z
  obtain ⟨a, rfl⟩ := projectiveAffineFiberChartMap_surjective f V y z
  exact (AlgHom.congr_fun hψ' a).trans (AlgHom.congr_fun hψ a).symm

end LinearStudy
