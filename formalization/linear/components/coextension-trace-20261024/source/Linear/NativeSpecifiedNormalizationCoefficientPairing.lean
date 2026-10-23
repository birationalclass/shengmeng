module
public import Linear.NativeSpecifiedNormalizationTopDualityCoefficient
public import Linear.OriginalForgottenDualMapEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S M N : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable [AddCommGroup N] [Module K N] [Module (MvPolynomial σ K) N] [Module S N]
variable [IsScalarTower (MvPolynomial σ K) S N] [IsScalarTower K (MvPolynomial σ K) N] [IsScalarTower K S N]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (E : ℤ → Submodule K N) [DirectSum.Decomposition E]
variable (hRM : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hSM : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hRN : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable (hSN : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M] [Module.IsTorsionFree S N]
variable [IsNoetherianRing S] [Algebra.FiniteType K S] [Module.Finite (MvPolynomial σ K) S]
variable [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
variable [Module.Finite (MvPolynomial σ K) N] [Module.Finite S N]
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
  integerGradedHomPrecomposition nativeProjectiveModuleSheaf nativeProjectiveDegreeZeroSheafMap
/-- Pointwise value of the SAME original actual-top dual comparison on
an ORIGINAL coefficient map,all integer twists. The RHS is the ACTUAL
dual of precomposition by the ORIGINAL R-restriction. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientValue
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (x : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hSM k) (q+1)) :
    (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) E
        (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B E hRN hSN c hc hgenC q hcard k).hom
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
          (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k)) (q+1) x)) =
    (integerGradedHomPrecomposition (MvPolynomial.homogeneousSubmodule σ K) D E
      (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k)).dualMap
      (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
          (-(Fintype.card σ:ℤ)-k)) from
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hRM hSM c hc hgenC q hcard k).hom x) := by
  apply LinearMap.ext
  intro psi
  let VN := ModuleCat.of K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) E
    (-(Fintype.card σ:ℤ)-k))
  let VM := ModuleCat.of K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
    (-(Fintype.card σ:ℤ)-k))
  let p : VN ⟶ VM := ModuleCat.ofHom
    (integerGradedHomPrecomposition (MvPolynomial.homogeneousSubmodule σ K) D E
      (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k))
  have he := nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient
    B D E hRM hSM hRN hSN f hf c hc hgenC q hcard k
  have hp := originalSpecifiedEvaluationPairing_of_coefficientSquare VN VM
    (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hRM hSM c hc hgenC q hcard k)
    (nativeFiniteNormalization_specifiedActualTopHomDualIso B E hRN hSN c hc hgenC q hcard k)
    ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology (Proj B)) (q+1)).map
      ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k))) p he x psi
  simpa only [p,ModuleCat.hom_ofHom,CategoryTheory.Sheaf.functorH,
    AddCommGrpCat.hom_ofHom,LinearMap.dualMap_apply] using hp
/-- The ORIGINAL specified evaluation is natural in coefficients:
B_N(H(f)x,psi)=B_M(x,psi∘f). The composition is the actual old homogeneous
Hom precomposition map,whose pointwise value is already proved.
No geometric trace or Koszul connecting-map transpose claim. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientPairing
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (x : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hSM k) (q+1))
    (psi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) E (-(Fintype.card σ:ℤ)-k)) :
    (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) E
        (-(Fintype.card σ:ℤ)-k)) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B E hRN hSN c hc hgenC q hcard k).hom
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
          (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k)) (q+1) x)) psi =
      (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
          (-(Fintype.card σ:ℤ)-k)) from
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hRM hSM c hc hgenC q hcard k).hom x)
      (integerGradedHomPrecomposition (MvPolynomial.homogeneousSubmodule σ K) D E
        (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k) psi) := by
  simpa only [LinearMap.dualMap_apply] using congrArg
    (fun ell : Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) E
      (-(Fintype.card σ:ℤ)-k)) => ell psi)
    (nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientValue
      B D E hRM hSM hRN hSN f hf c hc hgenC q hcard k x)
end LinearStudy
