module
public import Linear.ProjectiveNativeBaseDualSections
public import Linear.ProjectiveNativeAffinePushforwardDuality
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

/-- Actual sections of the native dual sheaf on the original V are
equivalent to functionals on the genuine finite affine pushforward O.
Both comparisons are constructed from original fractions and modules.
This local duality is proved, while global gluing and canonical identification
remain separate obligations. -/
theorem projectiveNormalization_native_sections_affine_pushforward_duality
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
    IsFinite g ∧ Nonempty
      (nativeProjectiveModuleSections 𝓑 𝒟 hD 0
        (op (Proj.basicOpen 𝓑 (φ (MvPolynomial.X i)))) ≃
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
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let a : A := MvPolynomial.X i
  have ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  have haS : φ a ∈ 𝓑 1 := (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha
  let z : nativeGradedModuleAwayZero 𝓑 𝒟 (φ a) ≃
      nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 (φ a) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by
      simp only [Equiv.refl_apply,nativeGradedModuleAwayDegreeZero_one])
  let e := z.trans (Equiv.ofBijective
    (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 (φ a) haS)
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i haS))
  dsimp only
  refine ⟨nativeNormalizationAffineChart_isFinite 𝒜 𝓑 a ha,⟨?_⟩⟩
  exact (e.symm.trans (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm).trans
    (nativeFullSourceAffinePushforwardDualEquiv 𝒜 𝓑 a ha
      (IsLocalization.injective (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))))
end LinearStudy
