module
public import Linear.NativeProjectiveExactFinitePresentation
public import Linear.ProjectiveDualNativeFreeSheafEpi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory Classical
variable {n r : ℕ}

/-- The ORIGINAL finite linear-normalization dual has a constructed
finite homogeneous presentation whose native associated sheaves are
genuinely exact, and whose last map is epi. The native kernel comparison
and exactness are proved from the actual original module maps.
Canonical identification and free-sheaf chart comparison are NOT inputs
or conclusions of this theorem. -/
theorem projectiveLinearNormalization_exists_exact_native_dual_presentation
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
    ∃ s : Finset D,
      letI := Classical.decEq s
      ∃ w : s → ℤ,
        let ℰ := integerShiftedFreePiece 𝓑 w
        let hE := integerShiftedFreePiece_smul_homogeneous 𝓑 w
        letI := integerShiftedFreeDecomposition 𝓑 w
        let e := integerShiftedFreeGeneratorMap (S := B) (fun i : s => (i : D))
        ∃ hh : ∀ d : ℤ, ∀ f : s → B, f ∈ ℰ d → e f ∈ 𝒟 d,
          Function.Surjective e ∧
            Epi (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e hh 0) ∧
            ∃ t : Finset e.ker,
              letI := Classical.decEq t
              ∃ z : t → ℤ,
                let ℛ := integerShiftedFreePiece 𝓑 z
                let hR := integerShiftedFreePiece_smul_homogeneous 𝓑 z
                letI := integerShiftedFreeDecomposition 𝓑 z
                let a := integerShiftedFreeGeneratorMap (S := B)
                  (fun i : t => ((i : e.ker) : s → B))
                ∃ ha : ∀ d : ℤ, ∀ f : t → B, f ∈ ℛ d → a f ∈ ℰ d,
                  ∃ hex : LinearMap.range a = e.ker,
                    (ShortComplex.mk
                      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℛ ℰ hR hE a ha 0)
                      (nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ 𝒟 hE hD e hh 0)
                      (nativeProjectiveDegreeZeroSheafMap_comp_zero 𝓑 ℛ ℰ 𝒟
                        hR hE hD a e ha hh hex 0)).Exact := by
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
  exact nativeProjectiveFiniteGraded_exists_exact_native_presentation 𝓑
    (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)

end LinearStudy
