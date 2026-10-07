module
public import Linear.ProjectiveSmoothOpenPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem affineChartPolynomialMap_homogeneous_mem_iff
    {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    (hX : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) ∉ I)
    (H : MvPolynomial (Fin (n + 1)) K) {m : ℕ} (hH : H.IsHomogeneous m) :
    affineChartPolynomialMap H ∈ I.map affineChartPolynomialMap.toRingHom ↔ H ∈ I := by
  refine ⟨?_, Ideal.mem_map_of_mem _⟩
  intro h
  let X0 : MvPolynomial (Fin (n + 1)) K := MvPolynomial.X 0
  let A := Localization.Away X0
  have ha := Ideal.mem_map_of_mem (projectiveChartLocalizationMap (K := K) (n := n)).toRingHom h
  rw [projectiveChartLocalizationMap_ideal I hI] at ha
  change projectiveChartLocalizationMap (affineChartPolynomialMap H) ∈
    I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) A) at ha
  rw [projectiveChartLocalizationMap_homogeneous H hH] at ha
  have hu : IsUnit (IsLocalization.Away.invSelf X0 (S := A)) :=
    IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf X0)
  have hm := (Ideal.unit_mul_mem_iff_mem _ (hu.pow m)).mp ha
  have hd := (I.disjoint_powers_iff_notMem_of_isPrime X0).mpr hX
  have hc := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers X0) A ‹I.IsPrime› hd
  change (I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) A)).comap
    (algebraMap (MvPolynomial (Fin (n + 1)) K) A) = I at hc
  change H ∈ (I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) A)).comap
    (algebraMap (MvPolynomial (Fin (n + 1)) K) A) at hm
  rwa [hc] at hm

/-- Surjectivity and total invariance keep a target chart coordinate from
vanishing identically on the original projective variety. -/
theorem projective_surjective_invariant_first_form_not_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : Function.Surjective f.onPoints) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    f.forms 0 ∉ V.ideal.toIdeal := by
  obtain ⟨z, hz⟩ := hf (normalizedProjectivePoint x0)
  have hzV : z ∈ V.zeroSet := by
    rw [← hV]
    change f.onPoints z ∈ V.zeroSet
    rwa [hz]
  induction z using Projectivization.ind with
  | h v hv =>
    intro hm
    have hzero := (V.mem_zeroSet_mk v hv).mp hzV (f.forms 0) hm
    rw [f.onPoints_mk] at hz
    change Projectivization.mk ℂ (f.evalVector v) (f.noBasePoint v hv) =
      Projectivization.mk ℂ (Fin.cases 1 x0) (normalizedCoordinateVector_ne_zero x0) at hz
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hz.symm
    have he := congrArg (fun w : CoordinateVector n => w 0) ha
    have : (0 : ℂ) = 1 := by
      simpa [HomogeneousEndomorphism.evalVector, Pi.smul_apply, smul_eq_mul, hzero] using he
    exact zero_ne_one this

theorem projective_surjective_invariant_affine_denominator_not_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : Function.Surjective f.onPoints) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    affineChartPolynomialMap (f.forms 0) ∉ V.affineIdeal := by
  letI := V.prime
  have hX : (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n) ∉ V.ideal.toIdeal := by
    intro hm
    have he := (V.normalizedPoint_mem_iff x0).mp hx0 _ hm
    simpa using he
  exact fun h => projective_surjective_invariant_first_form_not_mem f V hf hV x0 hx0
    ((affineChartPolynomialMap_homogeneous_mem_iff V.ideal.toIdeal V.ideal.isHomogeneous
      hX (f.forms 0) (f.homogeneous 0)).mp h)

/-- The actual rational denominator and source smoothness can be achieved
together from the original projective hypotheses. -/
theorem projective_surjective_invariant_exists_smooth_common_chart
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : Function.Surjective f.onPoints) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet),
      MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0 ∧
      Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal :=
  V.exists_smooth_affine_point_avoiding x0 hx0 (affineChartPolynomialMap (f.forms 0))
    (projective_surjective_invariant_affine_denominator_not_mem f V hf hV x0 hx0)

end LinearStudy
