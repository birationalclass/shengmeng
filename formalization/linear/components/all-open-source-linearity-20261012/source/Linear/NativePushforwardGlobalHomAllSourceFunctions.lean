module
public import Linear.NativePushforwardGlobalHomOriginalSourceAction
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

/-- The SAME original pushforward comparison preserves multiplication by
EVERY ACTUAL source function, not only a chosen homogeneous fraction.
Coverage by actual chart functions follows from mathlib's basicOpenIsoAway. -/
theorem nativeNormalizationPushforwardGlobalHomChartLinearEquiv_all_source_functions
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (hs : Function.Bijective
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 1 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)))
    (sb : Γ(Proj 𝓑,(nativeNormalizationProjectiveMap 𝒜 𝓑) ⁻¹ᵁ (Proj.basicOpen 𝒜 a)))
    (t : Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
        (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0),Proj.basicOpen 𝒜 a)) :
    let M := nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let U := Proj.basicOpen 𝒜 a
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs
      (schemePushforwardOriginalSourceActionSection f M U sb t) =
      schemePushforwardHomSourceActionSection f N U sb
        (nativeNormalizationPushforwardGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj hs t) := by
  dsimp only
  let e := Proj.basicOpenIsoAway 𝓑 (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide)
  obtain ⟨b,hb⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2
    (show Γ(Proj 𝓑,Proj.basicOpen 𝓑 (algebraMap R S a)) from sb)
  have hsb : (show Γ(Proj 𝓑,(nativeNormalizationProjectiveMap 𝒜 𝓑) ⁻¹ᵁ
      (Proj.basicOpen 𝒜 a)) from (Proj.awayToSection 𝓑 (algebraMap R S a)) b) = sb := hb
  rw [← hsb]
  exact nativeNormalizationPushforwardGlobalHomChartLinearEquiv_original_source_action
    𝒜 𝓑 a ha hinj hs b t
end LinearStudy
