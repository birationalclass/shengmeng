module
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.NativeNormalizationPushforwardChartModules
public import Linear.StructurePushforwardChartTopValueDirect
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
theorem nativeNormalizationPushforwardStructureChartModuleIso_top_value
    (a : R) (ha : a ∈ 𝒜 1)
    (r : Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf), Proj.basicOpen 𝒜 a)) :
    HEq ((nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha).hom.app ⊤
      (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).presheaf.map
          (eqToHom (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = Proj.basicOpen 𝒜 a by
            simp [Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
              Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op r))
    ((Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide)).inv.appTop
      ((Proj.basicOpen 𝓑 (algebraMap R S a)).topIso.inv r)) := by
  exact structurePushforwardChartTopValueDirect
    (nativeNormalizationProjectiveMap 𝒜 𝓑) (Proj.basicOpen 𝒜 a)
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) (by decide))
    (Proj.basicOpenIsoSpec 𝒜 a ha (by decide)) _
    (nativeNormalizationProjectiveMap_chart_restriction 𝒜 𝓑 a ha) r
end LinearStudy
