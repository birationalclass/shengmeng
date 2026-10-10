module
public import Linear.NormalizationWeightedSourceFraction
public import Linear.NativeGradedWeightedOverlap
public import Linear.NativeNormalizationSourceOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The constructed source degree-zero restriction, under the proved
complete source-chart equivalences, is EXACTLY mathlib's original Proj
restriction. This is equality of actual homogeneous chart elements. -/
theorem nativeNormalizationWeightedSourceChartEquiv_overlap
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) d a) :
    nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 (d+e) (a*b)
      (SetLike.mul_mem_graded ha hb)
      (nativeGradedModuleWeightedOverlapMap 𝒜 (nativeProjectiveRingIntegerPiece 𝓑)
        (normalizationSourceBaseGradeCompatibility 𝒜 𝓑) d e a b ha hb x) =
      HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b)
        (nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 d a ha x) := by
  have haB : algebraMap R S a ∈ 𝓑 d :=
    (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha
  obtain ⟨n,z,hz,hy⟩ := HomogeneousLocalization.Away.mk_surjective 𝓑 haB
    (nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 d a ha x)
  have hz' : z ∈ 𝓑 (n*d) := by simpa only [smul_eq_mul] using hz
  let x' : nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) d a :=
    ⟨LocalizedModule.mk z (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a),
      Submodule.subset_span ⟨n,z,by
        simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
          ite_true,Int.toNat_natCast] using hz',rfl⟩⟩
  have hxx' : x = x' := by
    apply (nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 d a ha).injective
    exact hy.symm.trans
      (nativeNormalizationWeightedSourceChartEquiv_homogeneous_fraction 𝒜 𝓑 d a ha haB n z hz').symm
  rw [hxx']
  apply HomogeneousLocalization.val_injective
  rw [nativeNormalizationWeightedSourceChartEquiv_val]
  change nativeNormalizationFullChartEquiv (S := S) (a*b)
    (originalLocalizedModuleAwayOverlap a b x'.val) = _
  dsimp only [x']
  rw [originalLocalizedModuleAwayOverlap_mk,nativeNormalizationFullChartEquiv_mk,
    nativeNormalizationWeightedSourceChartEquiv_homogeneous_fraction 𝒜 𝓑 d a ha haB n z hz',
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
  congr 1
  · rw [Algebra.smul_def,map_pow,mul_comm]
  · apply Subtype.ext
    exact map_pow (algebraMap R S) (a*b) n
end LinearStudy
