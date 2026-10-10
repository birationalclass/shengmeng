module
public import Linear.NativeFullSourceAffinePushforwardDual
public import Linear.NativeNormalizationAffineFinite
public import Linear.ProjectiveNativeDualChartsConstructed
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- Actual finite affine-chart duality for the original linear projection.
The comparison uses the whole source chart and the genuine pushforward
structure sheaf. Global Proj gluing and canonical identification are not
asserted by this chart result. -/
theorem projectiveNormalization_native_affine_pushforward_duality
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
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
    IsFinite g ∧ Nonempty
      (nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) (MvPolynomial.X i) ≃
        ((Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit (Spec (CommRingCat.of Bᵢ)).ringCatSheaf) ⟶
          SheafOfModules.unit (Spec (CommRingCat.of Aᵢ)).ringCatSheaf)) := by
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
  dsimp only
  refine ⟨nativeNormalizationAffineChart_isFinite 𝒜 𝓑 (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i), ⟨?_⟩⟩
  exact nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))

end LinearStudy
