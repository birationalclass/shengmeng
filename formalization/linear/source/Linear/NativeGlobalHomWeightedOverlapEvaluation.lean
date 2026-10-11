module
public import Linear.SchemeModuleHomAffineTransportLinear
public import Linear.NativeNormalizationWeightedChartModules
public import Linear.OriginalProjectiveWeightedChartScalarTransport
public import Linear.SchemeModuleHomTransportedEvaluation
public import Linear.NativeNormalizationWeightedSourceElementValue
public import Linear.NativeNormalizationGlobalWeightedAffineHomLinear
public import Linear.NativeGlobalWeightedHomEvaluation
public import Linear.ActualProjectiveChartOverlapPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
theorem nativeNormalizationGlobalHom_weighted_overlap_evaluation
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a))
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
    let γ := HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)
    schemeModuleHomSectionEvaluation M N (Proj.basicOpen 𝒜 (a*b))
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h)
      ((Proj.awayToSection 𝓑 (algebraMap R S (a*b))) (γ x)) =
      N.presheaf.map i.op
        (schemeModuleHomSectionEvaluation M N (Proj.basicOpen 𝒜 a) h
          ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)) := by
  dsimp only
  have hs : (Proj.awayToSection 𝓑 (algebraMap R S (a*b)))
      (HomogeneousLocalization.awayMap 𝓑
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
        (map_mul (algebraMap R S) a b) x) =
      (((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)).presheaf.map
          (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op)
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) x) := by
    have H := Proj.awayMap_awayToSection 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)
    exact congr($(H) x)
  rw [hs]
  exact schemeModuleHomSectionEvaluation_restrict _ _
    (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)) h _
theorem nativeNormalizationGlobalWeightedHom_original_overlap_values
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a))
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
    let φ := HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
    let γ := HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)
    let Ai := HomogeneousLocalization.Away 𝒜 a
    let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
    let Bi := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let Bij := HomogeneousLocalization.Away 𝓑 (algebraMap R S (a*b))
    let PA := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Ai Bi)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of Bi)).ringCatSheaf)
    let QA : (Spec (CommRingCat.of Ai)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Ai)).ringCatSheaf
    let PT := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap Aij Bij)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of Bij)).ringCatSheaf)
    let QT : (Spec (CommRingCat.of Aij)).Modules := SheafOfModules.unit (Spec (CommRingCat.of Aij)).ringCatSheaf
    let eA : tilde (R := CommRingCat.of Ai) (ModuleCat.of Ai Bi) ≅ PA := actualAffineAlgebraStructurePushforwardIso
    let eT : tilde (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ≅ PT := actualAffineAlgebraStructurePushforwardIso
    schemeModuleHomSectionEvaluation PT QT ⊤
      (nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 2 (by decide)
        (a*b) (SetLike.mul_mem_graded ha hb)
        ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h))
      (eT.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of Aij) (ModuleCat.of Aij Bij) ⊤) (γ x))) =
      (Spec.map (CommRingCat.ofHom φ)).appTop
        (schemeModuleHomSectionEvaluation PA QA ⊤
          (nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 1 (by decide) a ha h)
          (eA.hom.app ⊤ ((tilde.toOpen (R := CommRingCat.of Ai) (ModuleCat.of Ai Bi) ⊤) x))) := by
  dsimp only
  let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let i := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
  let γ := HomogeneousLocalization.awayMap 𝓑
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
    (map_mul (algebraMap R S) a b)
  have hi := nativeNormalizationGlobalWeightedAffineHomSections_original_section_chart_pullback
    𝒜 𝓑 1 (by decide) a ha h x
  have hij := nativeNormalizationGlobalWeightedAffineHomSections_original_section_chart_pullback
    𝒜 𝓑 2 (by decide) (a*b) (SetLike.mul_mem_graded ha hb)
    ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) (γ x)
  have he := nativeNormalizationGlobalHom_weighted_overlap_evaluation 𝒜 𝓑 a b ha hb h x
  have hs := actualProjectiveChartOverlapPullback 𝒜 a b ha hb
    (schemeModuleHomSectionEvaluation M N (Proj.basicOpen 𝒜 a) h
      ((Proj.awayToSection 𝓑 (algebraMap R S a)) x))
  exact hij.trans ((congrArg (fun z =>
    (Proj.basicOpenIsoSpec 𝒜 (a*b) (SetLike.mul_mem_graded ha hb) (by decide)).inv.appTop
      ((Proj.basicOpen 𝒜 (a*b)).topIso.inv z)) he).trans
    (hs.trans (congrArg (fun z => (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)))).appTop z) hi.symm)))
end LinearStudy
