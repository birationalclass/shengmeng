module
public import Linear.ProjectiveAffineFiberPointEquiv
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
variable {n : ℕ}

/-- Actual AMBIENT fiber equations, with no ideal of V added. Normal
nilpotents can remain in this quotient, as required by the residue argument. -/
def projectiveAmbientFiberIdeal (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (fun i : Fin n => affineChartPolynomialMap (f.forms i.succ) -
    MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)))

/-- No base point gives a nonzero denominator and the actual projective
fiber equation. Membership of V is not assumed or needed for this statement. -/
theorem projectiveAmbientFiberIdeal_point
    (f : HomogeneousEndomorphism n) (y z : Fin n → ℂ)
    (hz : z ∈ MvPolynomial.zeroLocus ℂ (projectiveAmbientFiberIdeal f y)) :
    MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0 ∧
      f.onPoints (normalizedProjectivePoint z) = normalizedProjectivePoint y := by
  let p0 := affineChartPolynomialMap (f.forms 0)
  let v : CoordinateVector n := Fin.cases 1 z
  have hev : ∀ i, MvPolynomial.eval z (affineChartPolynomialMap (f.forms i)) = f.evalVector v i :=
    fun i => AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) z) (f.forms i)
  have hrel (i : Fin n) :
      MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) = y i * MvPolynomial.eval z p0 := by
    have h := hz _ (Ideal.subset_span (Set.mem_range_self i))
    change MvPolynomial.eval z _ = 0 at h
    simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C, sub_eq_zero] using h
  have hp0 : MvPolynomial.eval z p0 ≠ 0 := by
    intro h0
    apply f.noBasePoint v (normalizedCoordinateVector_ne_zero z)
    funext i
    cases i using Fin.cases with
    | zero => exact (hev 0).symm.trans h0
    | succ i =>
      change f.evalVector v i.succ = 0
      rw [← hev i.succ, hrel i, h0, mul_zero]
  have hvec : f.evalVector v = MvPolynomial.eval z p0 • (Fin.cases 1 y : CoordinateVector n) := by
    funext i
    cases i using Fin.cases with
    | zero => simpa [Pi.smul_apply, smul_eq_mul] using (hev 0).symm
    | succ i => simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using (hev i.succ).symm.trans (hrel i)
  refine ⟨hp0, ?_⟩
  change f.onPoints (Projectivization.mk ℂ v _) = Projectivization.mk ℂ (Fin.cases 1 y) _
  rw [f.onPoints_mk]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨MvPolynomial.eval z p0, hvec.symm⟩

/-- The ambient fiber and the fiber inside V have the SAME point set,
derived from ORIGINAL total invariance. Their quotient rings need not agree. -/
theorem projectiveAmbientFiberIdeal_zeroLocus_eq_inside
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    MvPolynomial.zeroLocus ℂ (projectiveAmbientFiberIdeal f y) =
      MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y) := by
  ext z
  constructor
  · intro hz
    have hfy := (projectiveAmbientFiberIdeal_point f y z hz).2
    have hzV : normalizedProjectivePoint z ∈ V.zeroSet := by
      rw [← hV]
      change f.onPoints (normalizedProjectivePoint z) ∈ V.zeroSet
      rwa [hfy]
    exact projectiveAffineFiberIdeal_mem_of_point f V y z hzV hfy
  · intro hz
    intro P hP
    exact hz P ((show projectiveAmbientFiberIdeal f y ≤ projectiveAffineFiberIdeal f V y from
      le_sup_right) hP)

/-- Finiteness of the entire original projective map proves ambient fiber
finiteness, without declaring away its possible nilpotent structure. -/
theorem projectiveAmbientFiberIdeal_zeroLocus_finite
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : Fin n → ℂ) :
    (MvPolynomial.zeroLocus ℂ (projectiveAmbientFiberIdeal f y)).Finite := by
  have hF := f.onPoints_fibers_finite hq (normalizedProjectivePoint y)
  have hpre := hF.preimage normalizedProjectivePoint_injective.injOn
  apply hpre.subset
  intro z hz
  exact (projectiveAmbientFiberIdeal_point f y z hz).2

theorem projectiveAmbientFiberQuotient_finite
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : Fin n → ℂ) :
    Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAmbientFiberIdeal f y) :=
  polynomialQuotient_finite_of_finite_zeroLocus _ (projectiveAmbientFiberIdeal_zeroLocus_finite f hq y)

/-- The same closed point set gives equal radicals, not equal fiber ideals.
This is the correct bridge from the in-V fiber to the ambient residue algebra. -/
theorem projectiveAmbientFiberIdeal_radical_eq_inside
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    (projectiveAmbientFiberIdeal f y).radical = (projectiveAffineFiberIdeal f V y).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    projectiveAmbientFiberIdeal_zeroLocus_eq_inside f V hV y hy]

end LinearStudy
