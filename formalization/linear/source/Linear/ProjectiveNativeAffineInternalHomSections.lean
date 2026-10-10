module
public import Linear.ProjectiveNativeSectionsDualComparison
public import Linear.SchemeModuleHomTopSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- The SAME original finite linear normalization gives a specified
comparison between actual native dual chart sections and ACTUAL sections
of the constructed internal Hom O-MODULE sheaf on the original affine chart.
Global finite-projection gluing and canonical identification remain open. -/
def projectiveNormalization_native_sections_affine_internalHom_equiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
    letI : Module.Finite A B := hfinite
    let Aᵢ := HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)
    let Bᵢ := HomogeneousLocalization.Away 𝓑 (algebraMap A B (MvPolynomial.X i))
    let g := Spec.map (CommRingCat.ofHom (algebraMap Aᵢ Bᵢ))
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    nativeProjectiveModuleSections 𝓑 𝒟 hD 0
        (op (Proj.basicOpen 𝓑 (φ (MvPolynomial.X i)))) ≃
        Γ(schemeModuleHomModuleSheaf
          ((Scheme.Modules.pushforward g).obj
            (SheafOfModules.unit (Spec (CommRingCat.of Bᵢ)).ringCatSheaf))
          (SheafOfModules.unit (Spec (CommRingCat.of Aᵢ)).ringCatSheaf),⊤) := by
  dsimp only
  exact (projectiveNormalization_native_sections_affine_dual_equiv
    V L hL hinj hfinite i).trans (schemeModuleHomTopSectionsEquiv _ _).symm

end LinearStudy
