module
public import Linear.NativeSourceOverlapLocalizedSectionsEquiv
public import Linear.NativeFiniteGradedChartSectionsSurjective
public import Linear.ProjectiveNativeDualChartSectionsBijective
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

/-- Construct source weighted overlap sections for the SAME original V. Actual degree-one bijectivity, quasicoherence and torsion-freeness are derived. This is not yet an assertion that this new map equals the old degree-two chart-to-section map. -/
def projectiveNormalization_native_source_overlap_sections_linearEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i j : Fin (r+1)) :=
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
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  letI := coextensionGradedDecomposition 𝒜 𝓑
  letI := nativeCoextensionDual_finite_upper (R := A) (S := B)
  let q := Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal
  let coords : Fin (n+1) → B := fun j => q (MvPolynomial.X j)
  let hcoords : ∀ j, coords j ∈ 𝓑 1 :=
    fun j => ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j,rfl⟩
  let hgen : Algebra.adjoin ℂ (Set.range coords) = ⊤ := by
    calc
      Algebra.adjoin ℂ (Set.range coords) =
          Algebra.adjoin ℂ (q '' Set.range (MvPolynomial.X : Fin (n+1) → CoordinateRing n)) := by
        congr 1
        exact Set.range_comp q MvPolynomial.X
      _ = (Algebra.adjoin ℂ (Set.range (MvPolynomial.X : Fin (n+1) → CoordinateRing n))).map q :=
        (q.map_adjoin _).symm
      _ = q.range := by rw [MvPolynomial.adjoin_range_X,Algebra.map_top]
      _ = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective ℂ V.ideal.toIdeal)
  letI : Module.IsTorsionFree B D := by
    obtain ⟨m,hm,e,he,hhom⟩ :=
      projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
    exact he.moduleIsTorsionFree e (fun b d => e.map_smul b d)
  let ha := ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (MvPolynomial.isHomogeneous_X ℂ i))
  let hb := ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (MvPolynomial.isHomogeneous_X ℂ j))
  let hab : φ (MvPolynomial.X i)*φ (MvPolynomial.X j) ≠ 0 := by
    apply mul_ne_zero
    · intro h
      exact MvPolynomial.X_ne_zero (R := ℂ) i (hinj (h.trans φ.map_zero.symm))
    · intro h
      exact MvPolynomial.X_ne_zero (R := ℂ) j (hinj (h.trans φ.map_zero.symm))
  nativeSourceOverlapLocalizedSectionsLinearEquiv 𝓑 𝒟 hD
    coords hcoords hgen (φ (MvPolynomial.X i)) (φ (MvPolynomial.X j)) ha hb hab
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i ha)
end LinearStudy
