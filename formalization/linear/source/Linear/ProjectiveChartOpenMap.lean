module
public import Linear.ProjectiveChartMapCoordinates
public import Linear.AwayFractionEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

def projectiveChartDenominator (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) :
    MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal :=
  Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms 0))

def projectiveChartOpenPolynomialMap (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Localization.Away (projectiveChartDenominator f V) :=
  MvPolynomial.aeval (fun i : Fin n =>
    algebraMap _ (Localization.Away (projectiveChartDenominator f V))
      (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms i.succ))) *
        IsLocalization.Away.invSelf (projectiveChartDenominator f V))

theorem projectiveChartOpenPolynomialMap_fraction_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let L := FractionRing B
    (awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)).comp
        (projectiveChartOpenPolynomialMap f V) =
          (projectiveChartFractionMap f V hq hf hV x hx).comp
            ((IsScalarTower.toAlgHom ℂ B L).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal)) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro B L
  apply MvPolynomial.algHom_ext
  intro i
  change awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
      (projectiveChartOpenPolynomialMap f V (MvPolynomial.X i)) =
    projectiveChartFractionMap f V hq hf hV x hx
      (algebraMap B L (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i)))
  rw [projectiveChartFractionMap_coordinate]
  simp [projectiveChartOpenPolynomialMap, awayFractionEmbedding_algebraMap,
    awayFractionEmbedding_invSelf, projectiveChartDenominator, div_eq_mul_inv]

theorem projectiveChartOpenPolynomialMap_ideal
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    V.affineIdeal ≤ RingHom.ker (projectiveChartOpenPolynomialMap f V).toRingHom := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro P hP
  apply RingHom.mem_ker.mpr
  apply awayFractionEmbedding_injective (K := ℂ) (projectiveChartDenominator f V)
    (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
  change awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
        (projectiveChartOpenPolynomialMap f V P) =
    awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx) 0
  rw [map_zero]
  have h := AlgHom.congr_fun (projectiveChartOpenPolynomialMap_fraction_comp f V hq hf hV x hx) P
  change awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
        (projectiveChartOpenPolynomialMap f V P) =
    projectiveChartFractionMap f V hq hf hV x hx
      (algebraMap _ (FractionRing _) (Ideal.Quotient.mk V.affineIdeal P)) at h
  rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero, map_zero]

/-- Actual rational pullback on the dehomogenized coordinate domain, into its denominator open. -/
def projectiveChartOpenMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      Localization.Away (projectiveChartDenominator f V) :=
  Ideal.Quotient.liftₐ V.affineIdeal (projectiveChartOpenPolynomialMap f V)
    (fun P hP => RingHom.mem_ker.mp (projectiveChartOpenPolynomialMap_ideal f V hq hf hV x hx hP))

theorem projectiveChartOpenMap_mk
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) (P : MvPolynomial (Fin n) ℂ) :
    projectiveChartOpenMap f V hq hf hV x hx (Ideal.Quotient.mk V.affineIdeal P) =
      projectiveChartOpenPolynomialMap f V P := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem projectiveChartOpenMap_fraction_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let L := FractionRing B
    (awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)).comp
        (projectiveChartOpenMap f V hq hf hV x hx) =
          (projectiveChartFractionMap f V hq hf hV x hx).comp (IsScalarTower.toAlgHom ℂ B L) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro B L
  apply AlgHom.ext
  intro b
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  change awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
        (projectiveChartOpenMap f V hq hf hV x hx (Ideal.Quotient.mk V.affineIdeal P)) = _
  rw [projectiveChartOpenMap_mk]
  exact AlgHom.congr_fun (projectiveChartOpenPolynomialMap_fraction_comp f V hq hf hV x hx) P

end LinearStudy
