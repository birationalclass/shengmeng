module
public import Linear.NativeGradedDegreeOneOverlapLocalization
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
/-- The ORIGINAL coextension is torsion-free over its normalization BASE.
The proof compares its actual native action with original functional values. -/
theorem nativeCoextensionNormalizationBase_isTorsionFree :
    Module.IsTorsionFree R
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let f : D → (S → R) := fun ell x => ell x
  have hf : Function.Injective f := by
    intro x y h
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    exact congrFun h
  apply hf.moduleIsTorsionFree f
  intro r ell
  funext x
  exact congrArg (fun q => q x)
    ((restrictedCoextensionDualEquiv (R := R) (S := S)).map_smul r ell)
/-- Construct the dual comparison on the GENUINE degree-two overlap from
the proved localization of the ORIGINAL native dual and actual finite source
dual. No weighted-duality, freeness or overlap-compatibility input supplied. -/
def nativeNormalizationWeightedOverlapDualLinearEquiv [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b))) :=
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
  E.symm.trans (normalizationHomogeneousAffineDualOverlapLinearEquiv 𝒜 𝓑 a b ha hb hinj)
end LinearStudy
