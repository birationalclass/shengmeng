module
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
public import Linear.HomogeneousDualImageIdeal
public import Linear.FiniteDomainDualNonzero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory
variable {n r : ℕ}

/-- Realize the actual original normalization dual as an actual nonzero
homogeneous ideal, with one positive degree shift. This is algebraic data
for projective sheafification, not an assumed canonical-sheaf model. -/
theorem projectiveLinearNormalization_exists_homogeneous_dual_image
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    ∃ m : ℕ, 0 < m ∧ ∃ I : HomogeneousIdeal (homogeneousQuotientPiece V.ideal.toIdeal),
      I.toIdeal ≠ ⊥ ∧ ∃ e : D ≃ₗ[B] I.toIdeal,
        ∀ d : ℤ, ∀ ell : D,
          ell ∈ coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
            (homogeneousQuotientPiece V.ideal.toIdeal) d →
          (e ell : B) = gradedIntegerProjection (homogeneousQuotientPiece V.ideal.toIdeal)
            (d+(m : ℤ)) (e ell : B) := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : Module.Finite A B := hfinite
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  letI := coextensionGradedDecomposition 𝒜 𝓑
  letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  obtain ⟨m,hm,e,he,hhom⟩ := projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
  let I := homogeneousDualImageIdeal 𝓑 𝒟 (m : ℤ) e hhom
  have hI : I.toIdeal ≠ ⊥ := by
    obtain ⟨ell,hell⟩ := coextensionDual_exists_nonzero_at_one (R := A) (S := B)
    intro hz
    have hezero : e ell = 0 := by
      have hmem : e ell ∈ I.toIdeal := ⟨ell,rfl⟩
      simpa only [hz,Submodule.mem_bot] using hmem
    have hellzero : ell = 0 := he (hezero.trans (map_zero e).symm)
    apply hell
    rw [hellzero]
    rfl
  refine ⟨m,hm,I,hI,homogeneousDualImageEquiv 𝓑 𝒟 (m : ℤ) e he hhom,?_⟩
  intro d ell hell
  exact hhom d ell hell

end LinearStudy
