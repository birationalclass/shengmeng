module
public import Linear.NativeNormalizationPushforwardSourceChartTilde
public import Linear.NativePushforwardGlobalHomAllSourceFunctions
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.ActualAffineAlgebraDualInternalHomLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
attribute [local irreducible] schemeModuleHomModuleSheaf
  nativeNormalizationPushforwardGlobalHomChartLinearEquiv

theorem nativeNormalizationDualPushforwardSourceChart_isQuasicoherent
    (a : R) (ha : a ∈ 𝒜 1)
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (hq : (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0).IsQuasicoherent) :
    (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0)).restrict
          (Proj.awayι 𝒜 a ha (by decide))).IsQuasicoherent := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
  let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
  letI : M.IsQuasicoherent := hq
  let e := nativeNormalizationPushforwardSourceChartTildeIso 𝒜 𝓑
    (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha hs
  exact (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).ringCatSheaf).prop_of_iso e inferInstance

theorem nativeNormalizationStructureSourceChart_isQuasicoherent
    (a : R) (ha : a ∈ 𝒜 1) :
    (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).restrict
        (Proj.awayι 𝒜 a ha (by decide))).IsQuasicoherent := by
  let e := nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha
  let t := actualAffineAlgebraStructurePushforwardIso
    (A := HomogeneousLocalization.Away 𝒜 a)
    (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
  exact (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))).ringCatSheaf).prop_of_iso
      (t ≪≫ e.symm) inferInstance
end LinearStudy
