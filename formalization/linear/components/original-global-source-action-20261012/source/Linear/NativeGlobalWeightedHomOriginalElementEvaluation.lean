module
public import Linear.SchemeModuleHomAffineTransportLinear
public import Linear.NativeNormalizationWeightedChartModules
public import Linear.OriginalProjectiveWeightedChartScalarTransport
public import Linear.SchemeModuleHomTransportedEvaluation
public import Linear.NativeNormalizationWeightedSourceElementValue
public import Linear.NativeNormalizationGlobalWeightedAffineHomLinear
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
theorem nativeNormalizationGlobalWeightedAffineHomSections_original_element_evaluation
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a))
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let U := Proj.basicOpen 𝒜 a
    let e := Proj.basicOpenIsoSpec 𝒜 a ha hd
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let β := Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha hd)
    let y := M.presheaf.map (eqToHom
      (show Proj.awayι 𝒜 a ha hd ''ᵁ ⊤ = U by
        simp [U, Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)
    schemeModuleHomSectionEvaluation P Q ⊤
      (nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 d hd a ha h)
      ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) x)) =
      β.hom.app ⊤ ((schemeModuleHomCompositeRestriction M N U e.inv h).app ⊤ y) := by
  dsimp only
  have hs := nativeNormalizationWeightedSourceChart_affine_element 𝒜 𝓑 d hd a ha x
  refine (congrArg
    (fun z => schemeModuleHomSectionEvaluation _ _ ⊤
      (nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 d hd a ha h) z)
    hs.symm).trans ?_
  exact schemeModuleHomAffineTransportSectionsEquiv_top_transported_evaluation
    _ _ (Proj.basicOpen 𝒜 a) (CommRingCat.of (HomogeneousLocalization.Away 𝒜 a))
    (Proj.basicOpenIsoSpec 𝒜 a ha hd)
    (nativeNormalizationPushforwardWeightedStructureChartIso 𝒜 𝓑 d hd a ha)
    (Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha hd)) h _
end LinearStudy
