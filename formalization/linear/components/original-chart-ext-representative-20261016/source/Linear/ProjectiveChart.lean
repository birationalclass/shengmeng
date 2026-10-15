module
public import Linear.Projective
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Tactic
/-! Actual dehomogenization, degree and highest-component formulas, projective evaluation scaling and weighted homogeneous relations. For a base-point-free projective endomorphism, a coordinate hyperplane avoiding the chosen actual fiber gives the origin-only highest zero locus, with nonzero boundary forms explicit. Highest-part regularity is not proved here. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

def affineDehomogenize (P : MvPolynomial (Fin (n + 1)) K) : MvPolynomial (Fin n) K :=
  Polynomial.eval 1 (MvPolynomial.finSuccEquiv K n P)

theorem affineDehomogenize_degree (P : MvPolynomial (Fin (n + 1)) K) :
    (affineDehomogenize P).totalDegree ≤ P.totalDegree := by
  classical
  rw [affineDehomogenize, Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one, Polynomial.sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hh := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P i
    (Polynomial.mem_support_iff.mp hi)
  exact (Nat.le_add_right _ _).trans hh

theorem affineDehomogenize_eval (P : MvPolynomial (Fin (n + 1)) K) (z : Fin n → K) :
    MvPolynomial.eval z (affineDehomogenize P) =
      MvPolynomial.eval (Fin.cases 1 z) P := by
  simpa [affineDehomogenize] using
    (MvPolynomial.eval_polynomial_eval_finSuccEquiv (x := z) P (1 : MvPolynomial (Fin n) K))

theorem homogeneous_affine_chart_top_component
    (P : MvPolynomial (Fin (n + 1)) K) {q : ℕ} (hP : P.IsHomogeneous q) :
    MvPolynomial.homogeneousComponent q (affineDehomogenize P) =
      (MvPolynomial.finSuccEquiv K n P).coeff 0 := by
  classical
  rw [affineDehomogenize, Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one, Polynomial.sum, map_sum]
  rw [Finset.sum_eq_single 0]
  · exact MvPolynomial.homogeneousComponent_eq_self
      (hP.finSuccEquiv_coeff_isHomogeneous 0 q (zero_add q))
  · intro i hi hi0
    have hh := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P i
      (Polynomial.mem_support_iff.mp hi)
    apply MvPolynomial.homogeneousComponent_eq_zero
    have hp := hP.totalDegree_le
    omega
  · intro hi
    have hh : (MvPolynomial.finSuccEquiv K n P).coeff 0 = 0 :=
      by simpa only [Polynomial.mem_support_iff, not_not] using hi
    simp [hh]

theorem homogeneous_affine_chart_top_eval
    (P : MvPolynomial (Fin (n + 1)) K) {q : ℕ} (hP : P.IsHomogeneous q)
    (z : Fin n → K) :
    MvPolynomial.eval z (MvPolynomial.homogeneousComponent q (affineDehomogenize P)) =
      MvPolynomial.eval (Fin.cases 0 z) P := by
  rw [homogeneous_affine_chart_top_component P hP]
  simpa [← Polynomial.coeff_zero_eq_eval_zero] using
    (MvPolynomial.eval_polynomial_eval_finSuccEquiv (x := z) P (0 : MvPolynomial (Fin n) K))

theorem homogeneous_affine_chart_degree
    (P : MvPolynomial (Fin (n + 1)) K) {q : ℕ} (hP : P.IsHomogeneous q)
    (hn : (MvPolynomial.finSuccEquiv K n P).coeff 0 ≠ 0) :
    (affineDehomogenize P).totalDegree = q := by
  apply le_antisymm ((affineDehomogenize_degree P).trans hP.totalDegree_le)
  by_contra h
  have hlt : (affineDehomogenize P).totalDegree < q := by omega
  have he := MvPolynomial.homogeneousComponent_eq_zero q (affineDehomogenize P) hlt
  rw [homogeneous_affine_chart_top_component P hP] at he
  exact hn he

theorem homogeneous_affine_chart_eval
    (P : MvPolynomial (Fin (n + 1)) K) {t : ℕ} (hP : P.IsHomogeneous t)
    (v : Fin (n + 1) → K) (hv : v 0 ≠ 0) :
    MvPolynomial.eval v P = (v 0) ^ t *
      MvPolynomial.eval (fun i : Fin n => v i.succ / v 0) (affineDehomogenize P) := by
  let z : Fin n → K := fun i => v i.succ / v 0
  have hvec : (v 0) • Fin.cases 1 z = v := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp [z, Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hv]
  rw [affineDehomogenize_eval, ← homogeneous_eval_smul hP, hvec]

theorem homogeneous_affine_chart_relation {ι : Type*} [Fintype ι]
    (v : ι → Fin (n + 1) → K) (hv : ∀ i, v i 0 ≠ 0)
    (lam : ι → K) (hlam : ∀ i, lam i ≠ 0) (t : ℕ)
    (hrel : ∀ p : MvPolynomial (Fin n) K, p.totalDegree ≤ t →
      ∑ i, lam i * MvPolynomial.eval (fun j : Fin n => v i j.succ / v i 0) p = 0) :
    ∃ weights : ι → K, (∀ i, weights i ≠ 0) ∧
      ∀ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t →
        ∑ i, weights i * MvPolynomial.eval (v i) P = 0 := by
  refine ⟨fun i => lam i / (v i 0) ^ t, ?_, ?_⟩
  · intro i
    exact div_ne_zero (hlam i) (pow_ne_zero t (hv i))
  · intro P hP
    have hbound : (affineDehomogenize P).totalDegree ≤ t :=
      (affineDehomogenize_degree P).trans hP.totalDegree_le
    convert hrel (affineDehomogenize P) hbound using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [homogeneous_affine_chart_eval P hP (v i) (hv i)]
    field_simp [hv i]

theorem affine_highest_zeroLocus_of_no_infinity {ι : Type*}
    (F : ι → MvPolynomial (Fin (n + 1)) K) {q : ℕ} (hq : 0 < q)
    (hF : ∀ i, (F i).IsHomogeneous q)
    (hno : ∀ z : Fin n → K, z ≠ 0 →
      ∃ i, MvPolynomial.eval (Fin.cases 0 z) (F i) ≠ 0) :
    MvPolynomial.zeroLocus K (Ideal.span (Set.range (fun i =>
      MvPolynomial.homogeneousComponent q (affineDehomogenize (F i))))) = {0} := by
  rw [MvPolynomial.zeroLocus_span]
  ext z
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hzero
    obtain ⟨i, hi⟩ := hno z hzero
    have hh := hz i
    change MvPolynomial.eval z
      (MvPolynomial.homogeneousComponent q (affineDehomogenize (F i))) = 0 at hh
    rw [homogeneous_affine_chart_top_eval (F i) (hF i)] at hh
    exact hi hh
  · rintro rfl i
    change MvPolynomial.eval (0 : Fin n → K)
      (MvPolynomial.homogeneousComponent q (affineDehomogenize (F i))) = 0
    rw [homogeneous_affine_chart_top_eval (F i) (hF i)]
    have hzvec : (Fin.cases (0 : K) (0 : Fin n → K) : Fin (n + 1) → K) = 0 := by
      funext j
      cases j using Fin.cases <;> simp
    rw [hzvec]
    have hh := homogeneous_eval_smul (hF i) (0 : K) (0 : Fin (n + 1) → K)
    simpa [hq.ne'] using hh

theorem affine_actual_highest_zeroLocus_of_no_infinity {ι : Type*}
    (F : ι → MvPolynomial (Fin (n + 1)) K) {q : ℕ} (hq : 0 < q)
    (hF : ∀ i, (F i).IsHomogeneous q)
    (hn : ∀ i, (MvPolynomial.finSuccEquiv K n (F i)).coeff 0 ≠ 0)
    (hno : ∀ z : Fin n → K, z ≠ 0 →
      ∃ i, MvPolynomial.eval (Fin.cases 0 z) (F i) ≠ 0) :
    MvPolynomial.zeroLocus K (Ideal.span (Set.range (fun i =>
      MvPolynomial.homogeneousComponent (affineDehomogenize (F i)).totalDegree
        (affineDehomogenize (F i))))) = {0} := by
  have hd : ∀ i, (affineDehomogenize (F i)).totalDegree = q :=
    fun i => homogeneous_affine_chart_degree (F i) (hF i) (hn i)
  simpa only [hd] using affine_highest_zeroLocus_of_no_infinity F hq hF hno

theorem firstCoordinateVector_ne_zero (n : ℕ) :
    (Fin.cases (1 : ℂ) (0 : Fin n → ℂ) : CoordinateVector n) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp at hh

def standardProjectivePoint (n : ℕ) : ProjectivePoint n :=
  Projectivization.mk ℂ (Fin.cases 1 (0 : Fin n → ℂ)) (firstCoordinateVector_ne_zero n)

theorem projectiveFiber_no_infinity (f : HomogeneousEndomorphism n)
    (havoid : ∀ v : CoordinateVector n, ∀ hv : v ≠ 0, v 0 = 0 →
      f.onPoints (Projectivization.mk ℂ v hv) ≠ standardProjectivePoint n) :
    ∀ z : Fin n → ℂ, z ≠ 0 →
      ∃ i : Fin n, MvPolynomial.eval (Fin.cases 0 z) (f.forms i.succ) ≠ 0 := by
  intro z hz
  let v : CoordinateVector n := Fin.cases 0 z
  let w : CoordinateVector n := f.evalVector v
  let u : CoordinateVector n := Fin.cases 1 (0 : Fin n → ℂ)
  have hvec : v ≠ 0 := by
    intro h
    apply hz
    funext j
    exact congrFun h j.succ
  have hw : w ≠ 0 := f.noBasePoint v hvec
  have hu : u ≠ 0 := firstCoordinateVector_ne_zero n
  by_contra h
  push Not at h
  have he : w = (w 0) • u := by
    funext i
    cases i using Fin.cases with
    | zero => simp [w, v, u]
    | succ j => simpa only [w, v, u, HomogeneousEndomorphism.evalVector, Pi.smul_apply,
        Fin.cases_succ, Pi.zero_apply, smul_eq_mul, mul_zero] using h j
  have hmk : Projectivization.mk ℂ w hw = Projectivization.mk ℂ u hu :=
    (Projectivization.mk_eq_mk_iff' ℂ w u hw hu).mpr ⟨w 0, he.symm⟩
  have hon : f.onPoints (Projectivization.mk ℂ v hvec) = Projectivization.mk ℂ w hw :=
    f.onPoints_mk v hvec
  exact havoid v hvec rfl (hon.trans hmk)

theorem projectiveFiber_actual_highest_zeroLocus (f : HomogeneousEndomorphism n)
    (hq : 0 < f.degree)
    (hn : ∀ i : Fin n, (MvPolynomial.finSuccEquiv ℂ n (f.forms i.succ)).coeff 0 ≠ 0)
    (havoid : ∀ v : CoordinateVector n, ∀ hv : v ≠ 0, v 0 = 0 →
      f.onPoints (Projectivization.mk ℂ v hv) ≠ standardProjectivePoint n) :
    MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range (fun i : Fin n =>
      MvPolynomial.homogeneousComponent (affineDehomogenize (f.forms i.succ)).totalDegree
        (affineDehomogenize (f.forms i.succ))))) = {0} :=
  affine_actual_highest_zeroLocus_of_no_infinity (fun i : Fin n => f.forms i.succ)
    hq (fun i => f.homogeneous i.succ) hn (projectiveFiber_no_infinity f havoid)

end LinearStudy
