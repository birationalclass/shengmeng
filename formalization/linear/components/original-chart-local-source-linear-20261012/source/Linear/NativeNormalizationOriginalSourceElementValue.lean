module
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.NativeNormalizationPushforwardChartModules
public import Linear.NativeNormalizationOriginalChartTopValue
public import Linear.OriginalProjectiveChartScalarTransport
public import Linear.ActualAffineStructureElementValue
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
theorem nativeNormalizationOriginalSourceChart_element_value
    (a : R) (ha : a ∈ 𝒜 1)
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    HEq ((nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha).hom.app ⊤
      (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).presheaf.map
          (eqToHom (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = Proj.basicOpen 𝒜 a by
            simp [Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
              Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
            ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)))
      ((Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)))).inv x) := by
  have h := nativeNormalizationPushforwardStructureChartModuleIso_top_value
    𝒜 𝓑 a ha ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)
  have hs := congr($(originalProjectiveChartScalarTransport
    𝓑 (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)) x)
  exact h.trans (heq_of_eq hs)
theorem nativeNormalizationOriginalSourceChart_affine_element
    (a : R) (ha : a ∈ 𝒜 1)
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    ((nativeNormalizationPushforwardStructureChartModuleIso 𝒜 𝓑 a ha).hom.app ⊤
      (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).presheaf.map
          (eqToHom (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = Proj.basicOpen 𝒜 a by
            simp [Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
              Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
            ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)))
      = (actualAffineAlgebraStructurePushforwardIso
        (A := HomogeneousLocalization.Away 𝒜 a)
        (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a))).hom.app ⊤
        ((tilde.toOpen (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))
          (ModuleCat.of (HomogeneousLocalization.Away 𝒜 a)
            (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) ⊤) x) := by
  have hs := nativeNormalizationOriginalSourceChart_element_value 𝒜 𝓑 a ha x
  have he := actualAffineAlgebraStructurePushforwardIso_element_value
    (A := HomogeneousLocalization.Away 𝒜 a)
    (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) x
  exact eq_of_heq (hs.trans he.symm)
end LinearStudy
