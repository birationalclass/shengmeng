module
public import Linear.HomogeneousRationalIdeal
public import Mathlib.RingTheory.Localization.Ideal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {K : Type*} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveChartLocalizationMap : MvPolynomial (Fin n) K →ₐ[K] Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) :=
  MvPolynomial.aeval (fun i => algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i.succ) *
    IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))

def projectiveChartSpecialization : Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) →ₐ[K] MvPolynomial (Fin n) K :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)
    (f := affineChartPolynomialMap) (by simp [affineChartPolynomialMap])

theorem projectiveChartSpecialization_algebraMap (H : MvPolynomial (Fin (n + 1)) K) :
    projectiveChartSpecialization (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) H) =
      affineChartPolynomialMap H := by
  simp [projectiveChartSpecialization]

theorem projectiveChartSpecialization_invSelf :
    projectiveChartSpecialization (K := K) (n := n) (IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) = 1 := by
  have h := congrArg (projectiveChartSpecialization (K := K) (n := n))
    (IsLocalization.Away.mul_invSelf (S := Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))
  simpa only [map_mul, map_one, projectiveChartSpecialization_algebraMap,
    affineChartPolynomialMap, MvPolynomial.aeval_X, Fin.cases_zero, one_mul] using h

theorem projectiveChartSpecialization_leftInverse :
    (projectiveChartSpecialization (K := K) (n := n)).comp projectiveChartLocalizationMap =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [projectiveChartLocalizationMap, projectiveChartSpecialization_algebraMap,
    projectiveChartSpecialization_invSelf, affineChartPolynomialMap]

theorem projectiveChartLocalizationMap_homogeneous
    (H : MvPolynomial (Fin (n + 1)) K) {m : ℕ} (hH : H.IsHomogeneous m) :
    projectiveChartLocalizationMap (affineChartPolynomialMap H) =
      (IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) (S := Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) ^ m *
        algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) H := by
  have he := affineChartPolynomialMap_comp_aeval (K := K)
    (fun i : Fin n => algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i.succ) *
      IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))
  change MvPolynomial.aeval _ (affineChartPolynomialMap H) = _
  rw [← AlgHom.comp_apply, he]
  have hv : Fin.cases 1
      (fun i : Fin n => algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i.succ) *
        IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) =
      (fun i => IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) *
        algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i)) := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero]
      rw [mul_comm]
      exact (IsLocalization.Away.mul_invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)).symm
    | succ i => simp [mul_comm]
  rw [hv, homogeneous_aeval_smul hH]
  congr 1
  have hmap : MvPolynomial.aeval
      (fun i => algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X i)) =
        IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [hmap]
  rfl

theorem projectiveChartLocalizationMap_ideal
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) :
    (I.map affineChartPolynomialMap.toRingHom).map projectiveChartLocalizationMap.toRingHom =
      I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) := by
  rw [Ideal.map_map]
  apply homogeneous_ideal_maps_eq_of_unit_scaling I hI
  intro H m hH
  have hu : IsUnit (IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) (S := Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) :=
    IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))
  obtain ⟨u, hu⟩ := hu.pow m
  refine ⟨u, ?_⟩
  change projectiveChartLocalizationMap (affineChartPolynomialMap H) = _
  rw [projectiveChartLocalizationMap_homogeneous H hH, ← hu]

theorem projectiveChartLocalizationMap_comap_ideal
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) :
    (I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)))).comap projectiveChartLocalizationMap.toRingHom =
      I.map affineChartPolynomialMap.toRingHom := by
  let D := affineChartPolynomialMap (K := K) (n := n)
  let ψ := projectiveChartLocalizationMap (K := K) (n := n)
  let φ := projectiveChartSpecialization (K := K) (n := n)
  have hφ : (I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)))).map φ.toRingHom = I.map D.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro H
    exact projectiveChartSpecialization_algebraMap H
  apply le_antisymm
  · intro a ha
    change ψ a ∈ I.map (algebraMap (MvPolynomial (Fin (n + 1)) K)
      (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) at ha
    have h := Ideal.mem_map_of_mem φ.toRingHom ha
    rw [hφ] at h
    have he : φ (ψ a) = a := congrArg (fun f => f a) projectiveChartSpecialization_leftInverse
    change φ (ψ a) ∈ I.map D.toRingHom at h
    rwa [he] at h
  · intro a ha
    have h := Ideal.mem_map_of_mem ψ.toRingHom ha
    rw [projectiveChartLocalizationMap_ideal I hI] at h
    exact h

theorem affineChartPolynomialMap_ideal_isPrime
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    (hx : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) ∉ I) : (I.map affineChartPolynomialMap.toRingHom).IsPrime := by
  have hd := (I.disjoint_powers_iff_notMem_of_isPrime (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)).mpr hx
  letI := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)) I ‹I.IsPrime› hd
  rw [← projectiveChartLocalizationMap_comap_ideal I hI]
  exact Ideal.comap_isPrime _ _


/-- Passing from the homogeneous cone to the chosen affine chart does not
annihilate a nonzero homogeneous ideal. -/
theorem affineChartPolynomialMap_ideal_ne_bot
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    (hI0 : I ≠ ⊥) : I.map affineChartPolynomialMap.toRingHom ≠ ⊥ := by
  intro hz
  have hmap : I.map (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) = ⊥ := by
    rw [← projectiveChartLocalizationMap_ideal I hI, hz, Ideal.map_bot]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin (n + 1)) K) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))) :=
    IsLocalization.injective (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin (n + 1))))
  exact hI0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp hmap)

end LinearStudy
