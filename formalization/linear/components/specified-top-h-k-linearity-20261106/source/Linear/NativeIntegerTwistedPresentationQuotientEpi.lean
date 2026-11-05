module
public import Linear.NativeIntegerMixedPresentationTopCokernel
public import Linear.NativeIntegerFreeTwistRegrading
public import Linear.IntegerShiftedFreeRegradingPresentation
public import Linear.NativeProjectiveTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    z d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

include hc honto hex hcard

/-- The ACTUAL original top ordered-Cech beta map is epi for EVERY
integer native twist. Derived directly from the EXISTING actual original presentation cokernel
and proved primal twist isomorphisms. No dual Hom expression is expanded;
no cohomological surjectivity certificate or finite-dimensionality assumed. -/
theorem coordinateNativeIntegerTwistedPresentationQuotient_epi (k : ℤ) :
    Epi ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w) D
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w)
          hD β hβ k))) := by
  let B := homogeneousSubmodule σ K
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let G := H ⋙ F
  let Dk := LinearStudy.integerGradingShift D k
  let hDk := LinearStudy.integerGradingShift_smul_homogeneous B D hD k
  letI : DirectSum.Decomposition Dk := LinearStudy.integerGradingShiftDecomposition D k
  let zk := fun i => z i-k
  let wk := fun j => w j-k
  let hck := LinearStudy.integerShiftedFreeRelation_regrade B z w c hc k
  let hβk := LinearStudy.integerShiftedFreeQuotient_regrade B w D β hβ k
  let e0 := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B zk) (LinearStudy.integerShiftedFreePiece B wk)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B zk)
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wk) c hck 0
  let b0 := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B wk) Dk
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B wk) hDk β hβk 0
  let ψ := coordinateNativeIntegerPresentationTopCokernelIso
    zk wk Dk hDk c β hck hβk honto hex n hcard
  have hq := coordinateNativeIntegerPresentationTopCokernelIso_quotient
    zk wk Dk hDk c β hck hβk honto hex n hcard
  change cokernel.π (H.map e0) ≫ ψ.hom = H.map b0 at hq
  haveI : Epi (H.map b0) := by
    rw [← hq]
    infer_instance
  haveI : Epi (G.map b0) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective (H.map b0)).mp inferInstance
  let γw := LinearStudy.nativeIntegerFreeTwistRegradingIso B w k
  let γM := LinearStudy.nativeProjectiveTwistRegradingIso B D hD k
  let b := LinearStudy.nativeProjectiveDegreeZeroSheafMap B
    (LinearStudy.integerShiftedFreePiece B w) D
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous B w) hD β hβ k
  have hprimal : γw.inv ≫ b0 ≫ γM.hom = b :=
    LinearStudy.nativeIntegerFreeTwistRegradingIso_quotient B w D hD β hβ k
  change Epi (G.map b)
  rw [← hprimal,G.map_comp,G.map_comp]
  infer_instance

end MvPolynomial
