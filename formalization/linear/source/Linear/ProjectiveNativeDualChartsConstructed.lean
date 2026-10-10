module
public import Linear.ProjectiveNativeFullSourceDualBijective
public import Linear.ProjectiveNormalizationSourceChartFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n : ℕ}

/-- Construct the SAME finite linear normalization from ORIGINAL V, with
bijective ACTUAL native dual comparisons at every original coordinate.
No canonical model or comparison bijectivity is an input. The canonical
sheaf and restriction/gluing identifications still have to be proved. -/
theorem projective_exists_normalization_native_bijective_dual_charts
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
      ∃ hL : ∀ i, (L i).IsHomogeneous 1,
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        ∃ hfinite : (projectiveLinearNormalizationMap V L).Finite,
        ∀ i : Fin (r+1),
          let A := MvPolynomial (Fin (r+1)) ℂ
          let B := CoordinateRing n ⧸ V.ideal.toIdeal
          let φ := projectiveLinearNormalizationMap V L
          letI : Algebra A B := φ.toRingHom.toAlgebra
          letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
          letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
            (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
          Module.Finite
            (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
              (MvPolynomial.X i))
            (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
              (algebraMap A B (MvPolynomial.X i))) ∧
          Function.Bijective (projectiveNormalizationNativeFullSourceDualMap V L hL hfinite i) := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_normalization_native_source_charts V x hx
  refine ⟨r,hr,hdim,L,hL,hinj,hfinite,?_⟩
  intro i
  exact ⟨projectiveNormalizationNativeSourceChart_finite V L hL hfinite i,
    projectiveNormalizationNativeFullSourceDualMap_bijective V L hL hfinite i⟩
end LinearStudy
