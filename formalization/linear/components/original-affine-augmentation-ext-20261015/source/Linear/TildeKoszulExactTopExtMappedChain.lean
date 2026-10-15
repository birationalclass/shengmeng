module
public import Linear.TildeNativeModuleExtMappedChain
public import Linear.KoszulExactTopExtCoefficients
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u

/-- ACTUAL affine Koszul MODULE Ext representative under native tilde
is the class of the SAME actual sheafified exterior complex,natural
quotient augmentation and SAME N-valued top functional. Positive
exactness is explicit at this affine boundary and derived by the
original-Setup chart theorem;no regularity of N or Ext bijection is used. -/
theorem tildeKoszulExactTopExtMappedChain
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (N : ModuleCat.{u} R)
    (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    tildeNativeModuleExtMappedChainLaw R (functionKoszulResolutionOfExact H he) (n+1)
      (ModuleCat.ofHom L) (koszulExactTopCoefficient_isCocycle n H he N L) :=
  tildeNativeModuleExtMappedChainLaw_proof R (functionKoszulResolutionOfExact H he) (n+1)
    (ModuleCat.ofHom L) (koszulExactTopCoefficient_isCocycle n H he N L)

end LinearStudy
