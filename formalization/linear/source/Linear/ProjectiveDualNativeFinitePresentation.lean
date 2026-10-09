module
public import Linear.NativeProjectiveFiniteGradedFinitePresentation
public import Linear.ProjectiveDualExactNativePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory Classical
variable {n r : ℕ}

/-- Finite presentation of the ACTUAL native associated sheaf of the
ORIGINAL finite linear-normalization dual. Its free chart sources and
cokernel presentations are constructed, not assumed. Identification
with the canonical sheaf remains a separate obligation. -/
theorem projectiveLinearNormalization_native_dual_isFinitePresentation
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
    letI : Module.Finite A B := hfinite
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    letI := coextensionGradedDecomposition 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsFinitePresentation := by
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
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  let : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  let := coextensionGradedDecomposition 𝒜 𝓑
  let := nativeCoextensionDual_finite_upper (R := A) (S := B)
  let a : Fin (n+1) → B :=
    fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i)
  have ha : ∀ i, a i ∈ 𝓑 1 :=
    fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i, rfl⟩
  exact nativeFiniteGraded_isFinitePresentation_of_cover 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) a ha
    (homogeneousQuotient_native_coordinate_chart_cover
      V.ideal.toIdeal V.ideal.isHomogeneous)

end LinearStudy
