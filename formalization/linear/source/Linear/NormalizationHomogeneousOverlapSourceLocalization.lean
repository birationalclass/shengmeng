module
public import Linear.NormalizationHomogeneousOverlapRingSquare
public import Linear.NormalizationSourceChartLinearMap
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
/-- The genuine source overlap is an algebra over the genuine base chart
via its ACTUAL restriction followed by normalization, not an assumed square. -/
@[reducible] def normalizationHomogeneousOverlapSourceBaseAlgebra
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) :
    Algebra (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) :=
  ((normalizationHomogeneousChartMap 𝒜 𝓑 (a*b)).comp
    (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b))).toAlgebra
/-- The ACTUAL base/source overlap scalar tower follows from the proved
ring square; no compatibility certificate is supplied. -/
theorem normalizationHomogeneousOverlapSource_scalarTower
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) :
    letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 d e a b ha hb
    letI := (HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)).toAlgebra
    IsScalarTower (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) := by
  letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 d e a b ha hb
  letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact normalizationHomogeneousChartMap_overlap_square 𝒜 𝓑 d e a b ha hb
/-- The actual source overlap is a module localization at the ORIGINAL
base ratio b^d/a^e. This reuses mathlib's homogeneous localization theorem. -/
theorem normalizationHomogeneousOverlapSource_isLocalizedModule
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) (hd : d ≠ 0) :
    letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 d e a b ha hb
    letI := (HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)).toAlgebra
    letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 d e a b ha hb
    IsLocalizedModule (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb))
      (IsScalarTower.toAlgHom (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b)))).toLinearMap := by
  letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 d e a b ha hb
  letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
  letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 d e a b ha hb
  apply isLocalizedModule_iff_isLocalization.mpr
  rw [Algebra.algebraMapSubmonoid_powers]
  change IsLocalization.Away
    (normalizationHomogeneousChartMap 𝒜 𝓑 a
      (HomogeneousLocalization.Away.isLocalizationElem ha hb)) _
  rw [normalizationHomogeneousChartMap_overlap_localization_element 𝒜 𝓑 d e a b ha hb]
  exact HomogeneousLocalization.Away.isLocalization_mul
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b) hd
end LinearStudy
