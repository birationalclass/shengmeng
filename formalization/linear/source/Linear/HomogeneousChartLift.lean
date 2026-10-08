module
public import Linear.ProjectiveCommonChart
public import Linear.AffineChartComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous lift of an actual multivariate affine polynomial. -/
def affineHomogeneousLift {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) : MvPolynomial (Fin (n+1)) K :=
  let q := MvPolynomial.rename Fin.succ p
  ∑ k ∈ Finset.range (q.totalDegree+1),
    MvPolynomial.X (0 : Fin (n+1))^(q.totalDegree-k) * MvPolynomial.homogeneousComponent k q

theorem affineChartPolynomialMap_rename_succ {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) :
    affineChartPolynomialMap (MvPolynomial.rename Fin.succ p) = p := by
  have he : (affineChartPolynomialMap (K := K) (n := n)).comp
      (MvPolynomial.rename Fin.succ) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [affineChartPolynomialMap]
  exact AlgHom.congr_fun he p

theorem affineHomogeneousLift_isHomogeneous {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) :
    (affineHomogeneousLift p).IsHomogeneous (MvPolynomial.rename Fin.succ p).totalDegree := by
  classical
  unfold affineHomogeneousLift
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simpa only [Nat.sub_add_cancel hle] using
    (MvPolynomial.isHomogeneous_X_pow (0 : Fin (n+1))
      ((MvPolynomial.rename Fin.succ p).totalDegree-k)).mul
        (MvPolynomial.homogeneousComponent_isHomogeneous k (MvPolynomial.rename Fin.succ p))

theorem affineChartPolynomialMap_homogeneousLift {K : Type*} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) : affineChartPolynomialMap (affineHomogeneousLift p) = p := by
  classical
  unfold affineHomogeneousLift
  simp only [map_sum,map_mul,map_pow]
  have hX : affineChartPolynomialMap (MvPolynomial.X (0 : Fin (n+1)) :
      MvPolynomial (Fin (n+1)) K) = 1 := by simp [affineChartPolynomialMap]
  simp only [hX,one_pow,one_mul]
  rw [← map_sum,MvPolynomial.sum_homogeneousComponent]
  exact affineChartPolynomialMap_rename_succ p

/-- Homogenizing the actual good-open equation, with X₀ as an extra factor,
ensures every avoiding projective point lies in the original affine good open. -/
theorem projective_exists_homogeneous_chart_avoidance {n : ℕ}
    (V : IntegralProjectiveEquations n)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (p : MvPolynomial (Fin n) ℂ) (hp : p ∉ V.affineIdeal) :
    ∃ (D : ℕ) (H : CoordinateRing n), H.IsHomogeneous D ∧ H ∉ V.ideal.toIdeal ∧
      ∀ v : CoordinateVector n, MvPolynomial.eval v H ≠ 0 →
        v 0 ≠ 0 ∧ MvPolynomial.eval (fun i : Fin n => v i.succ/v 0) p ≠ 0 := by
  classical
  letI := V.prime
  let J := affineHomogeneousLift p
  have hJHom := affineHomogeneousLift_isHomogeneous p
  have hJ : J ∉ V.ideal.toIdeal := by
    intro h
    have hm := Ideal.mem_map_of_mem affineChartPolynomialMap.toRingHom h
    change affineChartPolynomialMap J ∈ V.affineIdeal at hm
    rw [affineChartPolynomialMap_homogeneousLift] at hm
    exact hp hm
  have hX : (MvPolynomial.X (0 : Fin (n+1)) : CoordinateRing n) ∉ V.ideal.toIdeal := by
    intro h
    have he := (V.normalizedPoint_mem_iff x0).mp hx0 _ h
    simpa using he
  refine ⟨(MvPolynomial.rename Fin.succ p).totalDegree+1,J*MvPolynomial.X 0,
    hJHom.mul (MvPolynomial.isHomogeneous_X _ _),?_,?_⟩
  · exact fun h => (V.prime.mem_or_mem h).elim hJ hX
  · intro v hv
    rw [map_mul,MvPolynomial.eval_X] at hv
    obtain ⟨hvJ,hv0⟩ := mul_ne_zero_iff.mp hv
    refine ⟨hv0,?_⟩
    rw [homogeneous_affine_chart_eval J hJHom v hv0] at hvJ
    have hn := (mul_ne_zero_iff.mp hvJ).2
    rw [← affineChartPolynomialMap_eq_dehomogenize,
      affineChartPolynomialMap_homogeneousLift] at hn
    exact hn

end LinearStudy
