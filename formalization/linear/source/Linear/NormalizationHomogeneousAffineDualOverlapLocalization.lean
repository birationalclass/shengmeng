module
public import Linear.NormalizationHomogeneousOverlapSourceLocalization
public import Linear.NormalizationSourceChartFinite
public import Linear.FiniteFunctionalLocalizationEquiv
public import Mathlib.LinearAlgebra.Dual.BaseChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
  LocalizedModule.moduleOfIsLocalization
/-- Actual source overlap rings are the module localization of the
original source chart at b/a; this does not assume a chart model. -/
def normalizationHomogeneousSourceOverlapLinearEquiv
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) :
    letI := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
    letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 1 1 a b ha hb
    letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
    letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 1 1 a b ha hb
    letI : IsScalarTower (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝒜 (a*b))
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
    letI := normalizationHomogeneousOverlapSource_isLocalizedModule 𝒜 𝓑 1 1 a b ha hb (by decide)
    LocalizedModule (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb))
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
      ≃ₗ[HomogeneousLocalization.Away 𝒜 (a*b)]
        HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b)) := by
  letI := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 1 1 a b ha hb
  letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
  letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 1 1 a b ha hb
  letI : IsScalarTower (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝒜 (a*b))
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := normalizationHomogeneousOverlapSource_isLocalizedModule 𝒜 𝓑 1 1 a b ha hb (by decide)
  let f := (IsScalarTower.toAlgHom (HomogeneousLocalization.Away 𝒜 a)
    (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b)))).toLinearMap
  exact (IsLocalizedModule.iso
    (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb)) f).extendScalarsOfIsLocalization
        (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb))
        (HomogeneousLocalization.Away 𝒜 (a*b))
/-- Localization of the finite ORIGINAL affine chart dual is the dual of
the ACTUAL overlap ring. Finiteness comes from the original normalization,
and no free/CM or duality compatibility assumption is added. -/
def normalizationHomogeneousAffineDualOverlapLinearEquiv [Module.Finite R S]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b))) :
    letI := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
    letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 1 1 a b ha hb
    letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
    letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 1 1 a b ha hb
    letI : IsScalarTower (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝒜 (a*b))
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
    letI := normalizationHomogeneousOverlapSource_isLocalizedModule 𝒜 𝓑 1 1 a b ha hb (by decide)
    LocalizedModule (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb))
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a) →ₗ[HomogeneousLocalization.Away 𝒜 a]
        HomogeneousLocalization.Away 𝒜 a)
      ≃ₗ[HomogeneousLocalization.Away 𝒜 (a*b)]
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
          →ₗ[HomogeneousLocalization.Away 𝒜 (a*b)] HomogeneousLocalization.Away 𝒜 (a*b)) := by
  letI := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI := normalizationHomogeneousOverlapSourceBaseAlgebra 𝒜 𝓑 1 1 a b ha hb
  letI := (HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)).toAlgebra
  letI := normalizationHomogeneousOverlapSource_scalarTower 𝒜 𝓑 1 1 a b ha hb
  letI : IsScalarTower (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝒜 (a*b))
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := normalizationHomogeneousOverlapSource_isLocalizedModule 𝒜 𝓑 1 1 a b ha hb (by decide)
  letI := normalizationHomogeneousChart_finite 𝒜 𝓑 a ha
  exact (finiteFunctionalLocalizationEquiv
    (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb)) hinj).trans
      (Module.Dual.congr (normalizationHomogeneousSourceOverlapLinearEquiv 𝒜 𝓑 a b ha hb))
end LinearStudy
