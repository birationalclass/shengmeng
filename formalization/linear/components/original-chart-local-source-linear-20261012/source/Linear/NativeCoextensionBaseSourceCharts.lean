module
public import Linear.NativeGradedBaseSourceMap
public import Linear.CoextensionBaseGradeCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization

/-- The original finite dual's two actual chart modules are compared by
the original universal localization map. Their grade compatibility is
derived from the original ring map and native dual action. -/
def nativeCoextensionBaseSourceChartEquiv (a : R) (ha : a ∈ 𝒜 1) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 1 a ≃
      nativeGradedModuleAwayDegreeZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) 1 (algebraMap R S a) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  exact nativeGradedBaseSourceChartEquiv 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 a ha
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)

/-- Exact comparison of the original unweighted degree-one chart types. -/
def nativeCoextensionBaseSourceZeroChartEquiv (a : R) (ha : a ∈ 𝒜 1) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a ≃
      nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) (algebraMap R S a) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let e := nativeGradedBaseSourceChartMap 𝒜 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
  exact Equiv.ofBijective e (nativeGradedBaseSourceChartMap_bijective 𝒜 𝓑
    (coextensionGradedPiece 𝒜 𝓑)
    (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha)

theorem nativeCoextensionBaseSourceZeroChartEquiv_apply (a : R) (ha : a ∈ 𝒜 1)
    (x : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha x).val =
      moduleBaseSourceLocalizationEquiv (S := S) a x.val := rfl

theorem nativeCoextensionBaseSourceChartEquiv_apply (a : R) (ha : a ∈ 𝒜 1)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) 1 a) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    (nativeCoextensionBaseSourceChartEquiv 𝒜 𝓑 a ha x).val =
      moduleBaseSourceLocalizationEquiv (S := S) a x.val := rfl
end LinearStudy
