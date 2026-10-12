module
public import Linear.NativeProjectiveFiniteFreeEpi
public import Linear.CoextensionHomogeneousGenerators
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.CoextensionProjectiveGradeCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory Classical
variable {n r : ℕ}

/-- The ORIGINAL finite linear-normalization dual receives a genuine
native sheaf epi from a constructed shifted finite free module. All
finite-generation and grading data come from the original finite map. -/
theorem projectiveLinearNormalization_exists_native_shiftedFree_sheafEpi
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    ∃ s : Finset D,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let ℱ := integerShiftedFreePiece 𝓑 w
        let hF := integerShiftedFreePiece_smul_homogeneous 𝓑 w
        let e := integerShiftedFreeGeneratorMap (S := B) (fun i : s => (i : D))
        ∃ hh : ∀ d : ℤ, ∀ f : s → B, f ∈ ℱ d → e f ∈ 𝒟 (d+0),
          Function.Surjective e ∧
            Epi (nativeProjectiveModuleSheafMap 𝓑 ℱ 𝒟 hF hD 0 e hh 0) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let : Module.Finite A B := hfinite
  let : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  let := coextensionGradedDecomposition 𝒜 𝓑
  let := nativeCoextensionDual_finite_upper (R := A) (S := B)
  exact nativeProjectiveFiniteGraded_exists_shiftedFree_sheafEpi 𝓑
    (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)

end LinearStudy
