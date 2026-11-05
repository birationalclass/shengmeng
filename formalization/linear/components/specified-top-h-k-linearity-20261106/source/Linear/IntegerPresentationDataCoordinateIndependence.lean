module
public import Linear.IntegerPresentationDataCoordinateNaturality
public import Linear.IntegerGradedHomPrecompositionIdentity
public import Linear.NativeProjectiveDegreeZeroIdentities
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ,∀ d : ℤ,∀ p : MvPolynomial σ K,p ∈ homogeneousSubmodule σ K t →
  ∀ x : M,x ∈ D d → p • x ∈ D ((t:ℤ)+d))
/-- ANY TWO actual finite homogeneous presentations yield the SAME
specified Cech/graded-Hom duality for every integer twist.
The original identity and its constructed homogeneous presentation lift
prove this equality;independence is not an assumed data field. -/
theorem coordinateNativeIntegerPresentationDataGradedHomDualIso_independent
    (P Q : LinearStudy.IntegerGradedFinitePresentationData (homogeneousSubmodule σ K) D)
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    coordinateNativeIntegerPresentationDataGradedHomDualIso D hD P n hcard k =
      coordinateNativeIntegerPresentationDataGradedHomDualIso D hD Q n hcard k := by
  apply Iso.ext
  have h := coordinateNativeIntegerPresentationDataGradedHomDualIso_naturality
    D D hD hD P Q (LinearMap.id : M →ₗ[MvPolynomial σ K] M) (fun _ _ hx => hx) n hcard k
  let T := (coordinateNativeCechHomologyFunctor (K:=K) (σ:=σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  have hid : T.map (LinearStudy.nativeProjectiveDegreeZeroSheafMap
      (homogeneousSubmodule σ K) D D hD hD (LinearMap.id : M →ₗ[MvPolynomial σ K] M)
      (fun _ _ hx => hx) k) = 𝟙 _ := by
    rw [LinearStudy.nativeProjectiveDegreeZeroSheafMap_id]
    exact T.map_id _
  change T.map _ ≫ _ = _ ≫ _ at h
  rw [hid,Category.id_comp,LinearStudy.integerGradedHomPrecomposition_id,
    LinearMap.dualMap_id,ModuleCat.ofHom_id,Category.comp_id] at h
  exact h.symm
/-- The finite-module choice of valid presentation data gives the SAME
specified comparison as every other valid presentation. -/
theorem coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_eq
    [Module.Finite (MvPolynomial σ K) M]
    (P : LinearStudy.IntegerGradedFinitePresentationData (homogeneousSubmodule σ K) D)
    (n : ℕ) (hcard : Fintype.card σ=n+2) (k : ℤ) :
    coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hD n hcard k =
      coordinateNativeIntegerPresentationDataGradedHomDualIso D hD P n hcard k :=
  coordinateNativeIntegerPresentationDataGradedHomDualIso_independent D hD
    (LinearStudy.integerGradedFiniteChosenPresentationData (homogeneousSubmodule σ K) D hD)
    P n hcard k
end MvPolynomial
