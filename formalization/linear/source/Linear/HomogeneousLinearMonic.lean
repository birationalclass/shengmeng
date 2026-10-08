module
public import Linear.ProjectiveChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}

/-- The linear shear fixes coordinate zero and adds a multiple of it
to each remaining coordinate. Unlike Nagata normalization, it preserves
the degree-one linear forms required by the original Bertini setup. -/
def homogeneousCoordinateShear (a : Fin n → K) :
    MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin (n+1)) K :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.X 0)
    (fun i => MvPolynomial.X i.succ + MvPolynomial.C (a i) * MvPolynomial.X 0))

theorem homogeneousCoordinateShear_comp_neg (a : Fin n → K) :
    (homogeneousCoordinateShear a).comp (homogeneousCoordinateShear (-a)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [homogeneousCoordinateShear,AlgHom.comp_apply]
  | succ i =>
    simp [homogeneousCoordinateShear,AlgHom.comp_apply]

def homogeneousCoordinateShearEquiv (a : Fin n → K) :
    MvPolynomial (Fin (n+1)) K ≃ₐ[K] MvPolynomial (Fin (n+1)) K :=
  AlgEquiv.ofAlgHom (homogeneousCoordinateShear a) (homogeneousCoordinateShear (-a))
    (homogeneousCoordinateShear_comp_neg a)
    (by simpa using homogeneousCoordinateShear_comp_neg (-a))

theorem homogeneousCoordinateShear_isHomogeneous (a : Fin n → K)
    (H : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hH : H.IsHomogeneous d) :
    (homogeneousCoordinateShear a H).IsHomogeneous d := by
  let g : Fin (n+1) → MvPolynomial (Fin (n+1)) K :=
    Fin.cases (MvPolynomial.X 0)
      (fun i => MvPolynomial.X i.succ + MvPolynomial.C (a i) * MvPolynomial.X 0)
  have hg (i : Fin (n+1)) : (g i).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero => exact MvPolynomial.isHomogeneous_X _ _
    | succ i =>
      exact (MvPolynomial.isHomogeneous_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa only [homogeneousCoordinateShear,one_mul] using hH.aeval g hg

theorem homogeneousCoordinateShear_axis_eval (a : Fin n → K)
    (H : MvPolynomial (Fin (n+1)) K) :
    MvPolynomial.eval (Fin.cases 1 (0 : Fin n → K)) (homogeneousCoordinateShear a H) =
      MvPolynomial.eval (Fin.cases 1 a) H := by
  have hh : (MvPolynomial.aeval (Fin.cases (1 : K) (0 : Fin n → K))).comp
      (homogeneousCoordinateShear a) = MvPolynomial.aeval (Fin.cases 1 a) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;> simp [homogeneousCoordinateShear,AlgHom.comp_apply]
  exact DFunLike.congr_fun hh H

/-- A nonzero homogeneous form cannot vanish on the whole coordinate-zero
affine chart over an infinite field. -/
theorem homogeneous_exists_chart_nonzero [Infinite K]
    (H : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hH : H.IsHomogeneous d) (hne : H ≠ 0) :
    ∃ a : Fin n → K, MvPolynomial.eval (Fin.cases 1 a) H ≠ 0 := by
  by_contra h
  push Not at h
  have hz : MvPolynomial.X 0 * H = 0 :=
    ((MvPolynomial.isHomogeneous_X K 0).mul hH).eq_zero_of_forall_eval_eq_zero (fun v => by
      by_cases hv : v 0 = 0
      · simp [hv]
      · have hval : MvPolynomial.eval v H = 0 := by
          rw [homogeneous_affine_chart_eval H hH v hv,affineDehomogenize_eval,h,mul_zero]
        simp [hval])
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) hne hz

/-- At the coordinate-zero axis the evaluation of a homogeneous form
is precisely the constant coefficient of its highest X_0 coefficient. -/
theorem homogeneous_axis_eval_coeff (H : MvPolynomial (Fin (n+1)) K)
    {d : ℕ} (hH : H.IsHomogeneous d) :
    MvPolynomial.eval (Fin.cases 1 (0 : Fin n → K)) H =
      MvPolynomial.eval (0 : Fin n → K) ((MvPolynomial.finSuccEquiv K n H).coeff d) := by
  classical
  let P := MvPolynomial.finSuccEquiv K n H
  have hnd : P.natDegree ≤ d := by
    dsimp [P]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree H 0).trans hH.totalDegree_le
  have hmap : Polynomial.map (MvPolynomial.eval (0 : Fin n → K)) P =
      Polynomial.monomial d (MvPolynomial.eval (0 : Fin n → K) (P.coeff d)) := by
    ext j
    by_cases hj : j = d
    · subst j
      simp
    · by_cases hlt : j < d
      · have hc : (P.coeff j).IsHomogeneous (d-j) :=
          hH.finSuccEquiv_coeff_isHomogeneous j (d-j) (by omega)
        have hz := hc.coeff_eq_zero (d := 0) (by simp; omega)
        simpa [MvPolynomial.eval_zero,MvPolynomial.constantCoeff,Polynomial.coeff_monomial,hj,Ne.symm hj]
          using hz
      · have hz : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hz,Polynomial.coeff_monomial,hj,Ne.symm hj]
  have hh := MvPolynomial.eval_eq_eval_mv_eval' (0 : Fin n → K) (1 : K) H
  rw [hmap] at hh
  have hcons : (Fin.cons (1 : K) (0 : Fin n → K) : Fin (n+1) → K) =
      (Fin.cases 1 (0 : Fin n → K) : Fin (n+1) → K) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [hcons] at hh
  simpa [P] using hh

/-- A genuine degree-one coordinate change makes any nonzero homogeneous
form monic up to a scalar in X_0. This is the first elimination step
needed for linear Noether normalization, not Bertini itself. -/
theorem homogeneous_exists_linear_unit_leadingCoeff [Infinite K]
    (H : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hH : H.IsHomogeneous d) (hne : H ≠ 0) :
    ∃ a : Fin n → K,
      IsUnit (MvPolynomial.finSuccEquiv K n (homogeneousCoordinateShearEquiv a H)).leadingCoeff := by
  obtain ⟨a,ha⟩ := homogeneous_exists_chart_nonzero H hH hne
  refine ⟨a,?_⟩
  let G := homogeneousCoordinateShear a H
  let P := MvPolynomial.finSuccEquiv K n G
  have hG : G.IsHomogeneous d := homogeneousCoordinateShear_isHomogeneous a H hH
  have heval : MvPolynomial.eval (0 : Fin n → K) (P.coeff d) ≠ 0 := by
    rw [← homogeneous_axis_eval_coeff G hG]
    exact (homogeneousCoordinateShear_axis_eval a H).trans_ne ha
  have hc0 : (P.coeff d).IsHomogeneous 0 := hG.finSuccEquiv_coeff_isHomogeneous d 0 (by omega)
  have hcoef : P.coeff d = MvPolynomial.C (MvPolynomial.eval (0 : Fin n → K) (P.coeff d)) := by
    have hz : (P.coeff d).totalDegree = 0 := Nat.eq_zero_of_le_zero hc0.totalDegree_le
    simpa [MvPolynomial.eval_zero,MvPolynomial.constantCoeff] using
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
  have hcne : P.coeff d ≠ 0 := by rw [hcoef]; exact MvPolynomial.C_ne_zero.mpr heval
  have hle : P.natDegree ≤ d := by
    dsimp [P]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree G 0).trans hG.totalDegree_le
  have hnd : P.natDegree = d := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcne
  change IsUnit P.leadingCoeff
  rw [Polynomial.leadingCoeff,hnd,hcoef]
  exact heval.isUnit.map MvPolynomial.C

end LinearStudy
