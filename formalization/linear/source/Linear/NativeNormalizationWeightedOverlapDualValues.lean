module
public import Linear.NativeNormalizationWeightedOverlapDualEquiv
public import Linear.NormalizationHomogeneousAffineDualOverlapValues
public import Linear.NativeDualFullSourceChartEquiv
public import Linear.CoextensionBaseGradeCompatibility
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Mathlib.Algebra.Module.Torsion.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra
/-- The constructed ORIGINAL native weighted dual preserves genuine
restriction of the original pairing on each actual source vector. -/
theorem nativeNormalizationWeightedOverlapDualLinearEquiv_restricted_value [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))
    (ell : nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 1 a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let N := nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)
  letI := nativeCoextensionNormalizationBase_isTorsionFree (R := R) (S := S)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  letI : Algebra Ai Aij := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI : IsScalarTower Ai Aij N := IsScalarTower.of_compHom Ai Aij N
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let P := Submonoid.powers t
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := nativeGradedDegreeOneOverlap_isLocalizedModule 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb hab
  let f := nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb
  let E1 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)).trans
    (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinja)
  let g := f.comp E1.symm.toLinearMap
  letI : IsLocalizedModule P g := inferInstance
  let E := (IsLocalizedModule.iso P g).extendScalarsOfIsLocalization P Aij
  nativeNormalizationWeightedOverlapDualLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj
      (nativeGradedModuleWeightedOverlapMap 𝒜 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell)
      (HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b) y) =
    HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) (E1 ell y) := by
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let N := nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)
  letI := nativeCoextensionNormalizationBase_isTorsionFree (R := R) (S := S)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  letI : Algebra Ai Aij := (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI : IsScalarTower Ai Aij N := IsScalarTower.of_compHom Ai Aij N
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let P := Submonoid.powers t
  letI := HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide : (1:ℕ)≠0)
  letI := nativeGradedDegreeOneOverlap_isLocalizedModule 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb hab
  let f := nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) a b ha hb
  let E1 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)).trans
    (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinja)
  let g := f.comp E1.symm.toLinearMap
  letI : IsLocalizedModule P g := inferInstance
  let E := (IsLocalizedModule.iso P g).extendScalarsOfIsLocalization P Aij
  change normalizationHomogeneousAffineDualOverlapLinearEquiv 𝒜 𝓑 a b ha hb hinj
    (E.symm (f ell))
    (HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b) y) = _
  have hfg : f ell = g (E1 ell) := by
    dsimp only [g,LinearMap.comp_apply,LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_apply]
  have hs : E.symm (f ell) = LocalizedModule.mk (E1 ell) 1 := by
    rw [hfg]
    exact IsLocalizedModule.iso_symm_apply' P g (g (E1 ell)) (E1 ell) 1 (by simp)
  rw [hs]
  exact normalizationHomogeneousAffineDualOverlapLinearEquiv_apply_mk
    𝒜 𝓑 a b ha hb hinj (E1 ell) y
end LinearStudy
