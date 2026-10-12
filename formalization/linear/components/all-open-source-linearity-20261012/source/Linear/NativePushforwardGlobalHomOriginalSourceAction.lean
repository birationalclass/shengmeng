module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
public import Linear.NativeNormalizationPushforwardGlobalHomSourceValues
public import Linear.SchemePushforwardOriginalSourceAction
public import Linear.NativePushforwardOriginalSourceChartValues
public import Linear.NativePushforwardOriginalSourceChartAction
public import Linear.NativeGlobalHomOriginalSourceAction
public import Linear.NativeAffineSourceChartHomLinear
public import Linear.NativeDualGlobalHomChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
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

/-- For EVERY section of the SAME actual native pushforward on the
original chart, the SAME original pushforward/global-Hom comparison
preserves the actual source-ring action. The actual source chart's
bijectivity is used, not a scalar compatibility certificate. -/
theorem nativeNormalizationPushforwardGlobalHomChartLinearEquiv_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (t : Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0),Proj.basicOpen 𝒜 a)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let U := Proj.basicOpen 𝒜 a
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let sb : Γ(Proj 𝓑,f ⁻¹ᵁ U) :=
      (show Γ(Proj 𝓑,f ⁻¹ᵁ U) from (Proj.awayToSection 𝓑 (algebraMap R S a)) b)
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
      (schemePushforwardOriginalSourceActionSection f M U sb t) =
      schemePushforwardHomSourceActionSection f N U sb
        (nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs t) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  dsimp only
  let θ := nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
    (hS := coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
  have hθ : Function.Surjective θ :=
    (nativeBaseSourceChartSectionMap_bijective 𝒜 𝓑 𝒟
      (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha hs).2
  obtain ⟨ell,hell⟩ := hθ t
  let d := nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell
  have ht : θ ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d) = t := by
    dsimp only [d]
    rw [Equiv.symm_apply_apply]
    exact hell
  rw [← ht]
  dsimp only [θ]
  rw [nativeNormalizationPushforwardChartSectionMap_original_source_action,
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv_apply_source_section,
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv_apply_source_section]
  exact nativeDualGlobalHomChartLinearEquiv_original_source_action 𝒜 𝓑 a ha hinj b d
end LinearStudy
