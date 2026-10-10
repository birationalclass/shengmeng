module
public import Linear.NativeFiniteGradedChartSectionsSurjective
public import Linear.ProjectiveNativeDualChartSectionsInjective
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
public import Linear.ProjectiveDualNativeFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
variable {n r : ℕ}

/-- Original finite linear normalization has a bijective comparison
between its actual degree-zero native dual chart and actual sections
of the original native dual sheaf. Surjectivity is derived from finite
graded generators and affine quasicoherent exactness. Torsion-freeness
for injectivity is derived from the original homogeneous embedding.
No chart comparison, free/CM condition or canonical identification is assumed. -/
theorem projectiveNormalization_native_dual_chart_sections_bijective
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
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    ∀ ha : φ (MvPolynomial.X i) ∈ 𝓑 1,
      Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1
        (φ (MvPolynomial.X i)) ha) := by
  letI := V.prime
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
  letI := coextensionGradedDecomposition 𝒜 𝓑
  letI := nativeCoextensionDual_finite_upper (R := A) (S := B)
  let q := Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal
  let coords : Fin (n+1) → B := fun j => q (MvPolynomial.X j)
  have hcoords : ∀ j, coords j ∈ 𝓑 1 :=
    fun j => ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j,rfl⟩
  have hgen : Algebra.adjoin ℂ (Set.range coords) = ⊤ := by
    calc
      Algebra.adjoin ℂ (Set.range coords) =
          Algebra.adjoin ℂ (q '' Set.range (MvPolynomial.X : Fin (n+1) → CoordinateRing n)) := by
        congr 1
        exact Set.range_comp q MvPolynomial.X
      _ = (Algebra.adjoin ℂ (Set.range (MvPolynomial.X : Fin (n+1) → CoordinateRing n))).map q :=
        (q.map_adjoin _).symm
      _ = q.range := by rw [MvPolynomial.adjoin_range_X,Algebra.map_top]
      _ = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective ℂ V.ideal.toIdeal)
  dsimp only
  intro ha
  exact ⟨projectiveNormalization_native_dual_chart_sections_injective
      V L hL hinj hfinite i ha,
    nativeFiniteGradedChartDegreeZeroSectionMap_surjective 𝓑
      (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)
      coords hcoords hgen (φ (MvPolynomial.X i)) ha⟩

end LinearStudy
