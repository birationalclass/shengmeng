module
public import Linear.NativeIntegerMixedPresentationCechHomDuality
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

/-- For EVERY ORIGINAL INTEGER native twist k,actual ordered top Cech
homology of SAME ORIGINAL M(k) is dual to ORIGINAL Hom_S(M,S)_(-N-k).
Original presentation maps c,beta and exactness are unchanged. Actual
weights regrade w->w-k;homogeneity and original Hom degree transport are
proved. The ORIGINAL shifted decomposition and ACTUAL native O-linear
regrading sheaf iso are reused,not supplied as certificates.
This is the actual OBJECT comparison;original twist/Koszul map naturality
and derived SHEAF cohomology remain separate. -/
def coordinateNativeIntegerTwistedPresentationGradedHomDualIso (k : ℤ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD k)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerGradedHomPiece (homogeneousSubmodule σ K) D
        (-(Fintype.card σ:ℤ)-k))) := by
  let B := homogeneousSubmodule σ K
  let Dk := LinearStudy.integerGradingShift D k
  let hDk := LinearStudy.integerGradingShift_smul_homogeneous B D hD k
  letI : DirectSum.Decomposition Dk := LinearStudy.integerGradingShiftDecomposition D k
  let zk := fun i => z i-k
  let wk := fun j => w j-k
  let hck := LinearStudy.integerShiftedFreeRelation_regrade B z w c hc k
  let hβk := LinearStudy.integerShiftedFreeQuotient_regrade B w D β hβ k
  let Ψ := coordinateNativeIntegerPresentationGradedHomDualIso
    zk wk Dk hDk c β hck hβk honto hex n hcard
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let ιk := LinearStudy.nativeProjectiveTwistRegradingIso B D hD k
  let ε := (LinearStudy.integerGradedHomRegradingEquiv B D k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  exact (G.mapIso ιk).symm.trans (Ψ.trans ε.symm)

end MvPolynomial
