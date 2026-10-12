module
public import Linear.NativeNormalizationWeightedChartSquare
public import Linear.NativeNormalizationPushforwardChartModules
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
/-- The actual global pushforward restricted to every positive-degree chart,
including original degree-two overlaps, is the actual corresponding affine pushforward. -/
def nativeNormalizationPushforwardWeightedChartModuleIso
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) (M : (Proj 𝓑).Modules) :
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M).restrict
      (Proj.awayι 𝒜 a ha hd) ≅
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
      (M.restrict (Proj.awayι 𝓑 (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd)) := by
  exact schemeModuleChartPushforwardRestrictionIso
    (nativeNormalizationProjectiveMap 𝒜 𝓑) (Proj.basicOpen 𝒜 a)
    (Proj.basicOpenIsoSpec 𝓑 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd)
    (Proj.basicOpenIsoSpec 𝒜 a ha hd) _
    (nativeNormalizationProjectiveMap_weighted_chart_restriction 𝒜 𝓑 d hd a ha) M
/-- Actual global structure pushforward chart identification in all positive degrees.
The structure-unit restrictions are actual mathlib isomorphisms. -/
def nativeNormalizationPushforwardWeightedStructureChartIso
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).restrict
      (Proj.awayι 𝒜 a ha hd) ≅
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).ringCatSheaf) :=
  nativeNormalizationPushforwardWeightedChartModuleIso 𝒜 𝓑 d hd a ha _ ≪≫
    (Scheme.Modules.pushforward _).mapIso
      (Scheme.Modules.restrictUnitIso
        (Proj.awayι 𝓑 (algebraMap R S a)
          ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) hd))
end LinearStudy
