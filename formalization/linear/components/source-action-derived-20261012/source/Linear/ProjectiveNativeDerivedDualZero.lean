module
public import Linear.NativeDerivedCoextensionZero
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
attribute [local instance] nativeCoextensionFunctor_additive MvPolynomial.gradedAlgebra
  coextensionGradedBaseModule
variable {n r : ℕ}

/-- For the ORIGINAL normalization-ring map of V and L, degree-zero
homology of the ACTUAL coextended injective resolution is isomorphic
as a B-module to the SAME native dual D. There is no normalized-dualizing
identification hypothesis or assertion in this calculation. -/
def projectiveNormalization_native_actual_coextended_homology_zero_iso
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let G := ModuleCat.coextendScalars (algebraMap A B)
    ∀ I : InjectiveResolution (ModuleCat.of A A),
      (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) 0).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
          G.obj (ModuleCat.of A A) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  dsimp only
  intro I
  exact nativeCoextendedInjectiveResolutionHomologyZeroIso
    (algebraMap A B) (ModuleCat.of A A) I

/-- In the SAME ORIGINAL integral projective setting and finite injective
linear projection, H^0 of the ACTUAL coextended complex admits a B-linear
injection into the original homogeneous coordinate quotient B. This is
an affine derived-dual consequence, not the global omega_V(r+1) embedding. -/
theorem projectiveNormalization_actual_coextended_homology_zero_exists_injection
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    let G := ModuleCat.coextendScalars (algebraMap A B)
    ∀ I : InjectiveResolution (ModuleCat.of A A),
      ∃ e : (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) 0).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) →ₗ[B] B,
          Function.Injective e := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  dsimp only
  intro I
  obtain ⟨m,hm,e,he,hhom⟩ :=
    projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
  let iso := projectiveNormalization_native_actual_coextended_homology_zero_iso V L I
  have hi : Function.Injective iso.hom.hom :=
    (ModuleCat.mono_iff_injective iso.hom).mp inferInstance
  exact ⟨e.comp iso.hom.hom,he.comp hi⟩

end LinearStudy
