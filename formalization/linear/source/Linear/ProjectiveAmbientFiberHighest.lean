module
public import Linear.ProjectiveFiberHighestRegular
public import Linear.ProjectiveAmbientFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {n : ℕ}

/-- Actual homogeneous equations for the ORIGINAL ambient fiber over [1:y].
The target is not replaced by an unrelated abstract map. -/
def projectiveAmbientFiberForms (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) :
    Fin n → CoordinateRing n :=
  fun i => f.forms i.succ - MvPolynomial.C (y i) * f.forms 0

theorem projectiveAmbientFiberForms_homogeneous
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ) (i : Fin n) :
    (projectiveAmbientFiberForms f y i).IsHomogeneous f.degree :=
  (f.homogeneous i.succ).sub ((f.homogeneous 0).C_mul (y i))

/-- Whole original projective fiber avoidance, already constructed by the
good-fiber theorem, rules out zeros of these SAME equations at infinity. -/
theorem projectiveAmbientFiberForms_no_infinity
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ)
    (havoid : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) :
    ∀ z : Fin n → ℂ, z ≠ 0 →
      ∃ i, MvPolynomial.eval (Fin.cases 0 z) (projectiveAmbientFiberForms f y i) ≠ 0 := by
  intro z hz
  let v : CoordinateVector n := Fin.cases 0 z
  have hv : v ≠ 0 := by
    intro h
    apply hz
    funext i
    exact congrFun h i.succ
  by_contra hall
  push Not at hall
  have hrel (i : Fin n) : f.evalVector v i.succ = y i * f.evalVector v 0 := by
    simpa only [projectiveAmbientFiberForms, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, sub_eq_zero,
      HomogeneousEndomorphism.evalVector] using hall i
  have hp0 : f.evalVector v 0 ≠ 0 := by
    intro h0
    apply f.noBasePoint v hv
    funext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i =>
      change f.evalVector v i.succ = 0
      rw [hrel i, h0, mul_zero]
  have hvec : f.evalVector v = (f.evalVector v 0) • (Fin.cases 1 y : CoordinateVector n) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa only [Pi.smul_apply, Fin.cases_succ, smul_eq_mul, mul_comm] using hrel i
  have hon : f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y := by
    rw [f.onPoints_mk]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨f.evalVector v 0, hvec.symm⟩
  exact havoid v hv hon rfl

/-- Exact degree, regular highest parts and origin-only highest zero locus
are derived from the ORIGINAL whole fiber; no separate boundary nonzero or
regular-sequence input is needed. -/
theorem projectiveAmbientFiberForms_actual_highest_regular
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : Fin n → ℂ)
    (havoid : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) :
    let P := fun i => affineDehomogenize (projectiveAmbientFiberForms f y i)
    (∀ i, (P i).totalDegree = f.degree) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) ℂ)
        (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range (fun i =>
        MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0} :=
  homogeneous_affine_exact_degree_and_highest_regular _ hq
    (projectiveAmbientFiberForms_homogeneous f y) (projectiveAmbientFiberForms_no_infinity f y havoid)

end LinearStudy
