module
public import Linear.ActualAffineAlgebraDualInternalHomLinear
public import Linear.NativeNormalizationGlobalWeightedAffineHomLinear
public import Linear.NativeNormalizationWeightedOverlapDualEquiv
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
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra
/-- The original native dual on the actual degree-two overlap corresponds
linearly to sections of the SAME actual global internal Hom. The map is the
proved native weighted functional, actual affine tilde map and original chart transport. -/
def nativeDualGlobalHomWeightedOverlapLinearEquiv [IsDomain R]
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0)
    (hinja : Function.Injective (algebraMap R (Localization.Away a)))
    (hinj : Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b))) :
    let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    letI := nativeNormalizationGlobalWeightedHomChartModule 𝒜 𝓑 2 (by decide) (a*b)
      (SetLike.mul_mem_graded ha hb)
    nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 2 (a*b)
      ≃ₗ[HomogeneousLocalization.Away 𝒜 (a*b)]
        Γ(schemeModuleHomModuleSheaf P Q,Proj.basicOpen 𝒜 (a*b)) := by
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
  dsimp only
  let E := nativeNormalizationWeightedOverlapDualLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj
  exact E.trans ((actualAffineAlgebraDualInternalHomSectionsLinearEquiv
      (A := HomogeneousLocalization.Away 𝒜 (a*b))
      (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b)))).trans
    (nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 2
      (by decide) (a*b) (SetLike.mul_mem_graded ha hb)).symm)

end LinearStudy
