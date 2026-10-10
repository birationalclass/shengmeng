module
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
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
/-- The actual source overlap equivalence retains the genuine overlap
map on every original source-chart vector. -/
theorem normalizationHomogeneousSourceOverlapLinearEquiv_apply_mk
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
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
    normalizationHomogeneousSourceOverlapLinearEquiv 𝒜 𝓑 a b ha hb
      (LocalizedModule.mk x 1) = HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b) x := by
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
  exact IsLocalizedModule.iso_mk_one
    (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb)) f x
/-- The actual affine dual-overlap comparison evaluates on the genuine
restricted source vector as the genuine restriction of the ORIGINAL value. -/
theorem normalizationHomogeneousAffineDualOverlapLinearEquiv_apply_mk
    [Module.Finite R S] (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (ψ : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a)
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
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
    normalizationHomogeneousAffineDualOverlapLinearEquiv 𝒜 𝓑 a b ha hb hinj
      (LocalizedModule.mk ψ 1)
      (HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b) x) =
      HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) (ψ x) := by
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
  let E := normalizationHomogeneousSourceOverlapLinearEquiv 𝒜 𝓑 a b ha hb
  change finiteFunctionalLocalizationEquiv
      (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb)) hinj
      (LocalizedModule.mk ψ 1)
      (E.symm (HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b) x)) = _
  rw [← normalizationHomogeneousSourceOverlapLinearEquiv_apply_mk 𝒜 𝓑 a b ha hb x]
  rw [LinearEquiv.symm_apply_apply]
  exact finiteFunctionalLocalizationEquiv_apply_mk
    (Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem ha hb)) hinj ψ x
end LinearStudy
