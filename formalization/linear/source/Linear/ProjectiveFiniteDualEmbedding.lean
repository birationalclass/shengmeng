module
public import Linear.CoextensionIntegralEmbedding
public import Linear.ProjectiveFiniteDualFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory
variable {n r : ℕ}

/-- Construct an actual linear embedding of the original normalization
dual into the original homogeneous coordinate domain. This is ungraded
and does not yet identify the module with a canonical sheaf or fix a twist. -/
theorem projectiveLinearNormalization_finiteDual_exists_embedding
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    ∃ e : (ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
      (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)) →ₗ[
        CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal),
      Function.Injective e := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Module.Finite A B := hfinite
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  exact coextensionDual_exists_integral_embedding (R := A) (S := B)

/-- Choose the actual original linear normalization and construct its
dual embedding from V. No generic embedding or denominator is an input. -/
theorem projective_exists_linear_normalization_with_dual_embedding
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∃ e : (ModuleCat.coextendScalars (projectiveLinearNormalizationMap V L).toRingHom).obj
          (ModuleCat.of (MvPolynomial (Fin (r+1)) ℂ) (MvPolynomial (Fin (r+1)) ℂ)) →ₗ[
            CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal),
          Function.Injective e := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_linear_normalization_chart_dimension V x hx
  exact ⟨r,hr,hdim,L,hL,hinj,hfinite,
    projectiveLinearNormalization_finiteDual_exists_embedding V L hinj hfinite⟩

end LinearStudy
