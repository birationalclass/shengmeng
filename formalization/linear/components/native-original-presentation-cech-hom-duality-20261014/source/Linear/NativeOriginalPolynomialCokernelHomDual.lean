module
public import Linear.NativeOriginalDegreeRelationDualCokernel
public import Linear.IntegerShiftedFreePresentationDualCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts MvPolynomial.gradedAlgebra
variable {K M : Type} [Field K] {σ : Type} [Fintype σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (a : I → ℕ) (b : J → ℕ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
/-- The ACTUAL ORIGINAL polynomial transpose matrix extracted from c has
cokernel equal to the K-dual of ORIGINAL Hom_S(M,S)_(-N),N=card(sigma).
The original entry matrix,degree-coordinate dual square,and homogeneous
presentation Hom kernel are all proved,not new comparison premises. -/
def coordinateOriginalPresentationPolynomialDualHomIso :
    cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b
      (coordinatePresentationPolynomialEntry a b c hc)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerGradedHomPiece (homogeneousSubmodule σ K) D (-(Fintype.card σ:ℤ)))) :=
  (coordinateOriginalDegreeRelationDualCokernelIso a b c hc).trans
    (LinearStudy.integerShiftedFreePresentationDualCokernelHomIso c
      (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i))
      (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
      D β hβ honto hex (-(Fintype.card σ:ℤ)))

/-- The polynomial-cokernel/Hom comparison preserves the ORIGINAL
quotient:the final functional uses the ORIGINAL coefficients phi(beta(e_j)). -/
theorem coordinateOriginalPresentationPolynomialDualHomIso_quotient :
    cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b
        (coordinatePresentationPolynomialEntry a b c hc)) ≫
      (coordinateOriginalPresentationPolynomialDualHomIso a b D c β hc hβ honto hex).hom =
    (coordinateOriginalDegreeCoefficientDualIso b).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreePresentationHomCoefficientMap c
        (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) hc
        D β hβ honto hex (-(Fintype.card σ:ℤ))).dualMap := by
  unfold coordinateOriginalPresentationPolynomialDualHomIso
  simp only [Iso.trans_hom]
  erw [← Category.assoc,coordinateOriginalDegreeRelationDualCokernelIso_quotient,Category.assoc]
  erw [LinearStudy.integerShiftedFreePresentationDualCokernelHomIso_quotient]

end MvPolynomial
