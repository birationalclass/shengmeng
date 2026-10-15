module
public import Linear.PolynomialFiniteZeroLocus
public import Linear.ProjectiveFibersFinite
public import Linear.ProjectiveAffineVariety
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

theorem normalizedProjectivePoint_injective :
    Function.Injective (normalizedProjectivePoint (n := n)) := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
  have ha1 : (a : ℂ) = 1 := by
    have h0 := congrFun ha 0
    change (a : ℂ) * 1 = 1 at h0
    simpa using h0
  funext i
  have hi := congrFun ha i.succ
  change (a : ℂ) * y i = x i at hi
  rw [ha1, one_mul] at hi
  exact hi.symm

/-- The actual polynomial ideal of a normalized projective fiber inside V. -/
def projectiveAffineFiberIdeal
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  V.affineIdeal ⊔ Ideal.span (Set.range (fun i : Fin n =>
    affineChartPolynomialMap (f.forms i.succ) -
      MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)))

/-- Every point of the actual polynomial fiber ideal maps to the specified
normalized target. The denominator is proved nonzero from no base point. -/
theorem projectiveAffineFiberIdeal_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y z : Fin n → ℂ)
    (hz : z ∈ MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)) :
    normalizedProjectivePoint z ∈ V.zeroSet ∧
      MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0 ∧
      f.onPoints (normalizedProjectivePoint z) = normalizedProjectivePoint y := by
  let p0 := affineChartPolynomialMap (f.forms 0)
  let v : CoordinateVector n := Fin.cases 1 z
  have hev : ∀ i, MvPolynomial.eval z (affineChartPolynomialMap (f.forms i)) = f.evalVector v i := by
    intro i
    exact AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) z) (f.forms i)
  have hrel (i : Fin n) :
      MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) = y i * MvPolynomial.eval z p0 := by
    have hi := hz _ (show affineChartPolynomialMap (f.forms i.succ) -
        MvPolynomial.C (y i) * p0 ∈ projectiveAffineFiberIdeal f V y from
      (show Ideal.span (Set.range (fun j : Fin n =>
        affineChartPolynomialMap (f.forms j.succ) - MvPolynomial.C (y j) * p0)) ≤
        projectiveAffineFiberIdeal f V y from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self i)))
    change MvPolynomial.eval z _ = 0 at hi
    rw [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C, sub_eq_zero] at hi
    exact hi
  have hp0 : MvPolynomial.eval z p0 ≠ 0 := by
    intro h0
    apply f.noBasePoint v (normalizedCoordinateVector_ne_zero z)
    funext i
    cases i using Fin.cases with
    | zero => exact (hev 0).symm.trans h0
    | succ i =>
      change f.evalVector v i.succ = 0
      rw [← hev i.succ, hrel i, h0, mul_zero]
  have hzV : normalizedProjectivePoint z ∈ V.zeroSet := by
    apply (V.normalizedPoint_mem_iff z).mpr
    intro H hH
    have ha := hz (affineChartPolynomialMap H)
      ((show V.affineIdeal ≤ projectiveAffineFiberIdeal f V y from le_sup_left)
        (Ideal.mem_map_of_mem affineChartPolynomialMap.toRingHom hH))
    have he := AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) z) H
    exact he.symm.trans ha
  have hvec : f.evalVector v = MvPolynomial.eval z p0 • (Fin.cases 1 y : CoordinateVector n) := by
    funext i
    cases i using Fin.cases with
    | zero => simpa [Pi.smul_apply, smul_eq_mul] using (hev 0).symm
    | succ i => simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hev i.succ).symm.trans (hrel i)
  refine ⟨hzV, hp0, ?_⟩
  change f.onPoints (Projectivization.mk ℂ v _) = Projectivization.mk ℂ (Fin.cases 1 y) _
  rw [f.onPoints_mk]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨MvPolynomial.eval z p0, hvec.symm⟩

theorem projectiveAffineFiberIdeal_zeroLocus_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (y : Fin n → ℂ) :
    (MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)).Finite := by
  have hF := f.onPoints_fibers_finite hq (normalizedProjectivePoint y)
  have hpre := hF.preimage normalizedProjectivePoint_injective.injOn
  apply hpre.subset
  intro z hz
  exact (projectiveAffineFiberIdeal_point f V y z hz).2.2

/-- The original projective fiber's actual affine scheme quotient is finite
dimensional, even before any reducedness theorem has been established. -/
theorem projectiveAffineFiberQuotient_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (y : Fin n → ℂ) :
    Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  exact polynomialQuotient_finite_of_finite_zeroLocus _
    (projectiveAffineFiberIdeal_zeroLocus_finite f V hq y)

end LinearStudy
