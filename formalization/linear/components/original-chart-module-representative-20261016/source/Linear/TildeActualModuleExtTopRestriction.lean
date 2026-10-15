module
public import Linear.TildeKoszulCoforkModuleExtIso
public import Linear.KoszulExactTopExtCoefficientRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u

/-- Evaluate the ACTUAL module Ext representative constructed from the
SAME affine SHEAF cocycle at the ordered top exterior generator,mod IN.
This is actual MODULE Ext,not a claimed internal sheaf Ext isomorphism. -/
theorem tildeActualCocycleModuleExt_topRestriction
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (N : ModuleCat.{u} R)
    (a : (tilde.functor R).obj ((functionKoszulResolutionOfExact H he).complex.X (n+1)) ⟶
      (tilde.functor R).obj N)
    (ha : (tilde.functor R).map ((functionKoszulResolutionOfExact H he).complex.d (n+2) (n+1)) ≫ a = 0) :
    koszulExactTopExtCoefficientRestrictionEquiv n H he N
      (tildeActualCocycleModuleExt R (functionKoszulResolutionOfExact H he) (n+1) a ha) =
      Submodule.Quotient.mk ((tildeActualFunctionalPreimage R a).hom (topKoszulGenerator (n+1))) := by
  change koszulExactTopExtCoefficientRestrictionEquiv n H he N
    (koszulExactTopExtCoefficientRepresentative n H he N (tildeActualFunctionalPreimage R a).hom) = _
  exact koszulExactTopExtCoefficientRestrictionEquiv_representative n H he N _

/-- Retain the ACTUAL coefficient iso lambda when evaluating the SAME
constructed module class. Equality with a separately prescribed original
local coordinate formula is not assumed or asserted. -/
theorem tildeKoszulIsoCocycleModuleExt_topRestriction
    (R : CommRingCat.{u}) (n : ℕ) (H : Fin (n+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X (n+1) ⟶ M)
    (ha : (tildeFunctionKoszulComplex R H).d (n+2) (n+1) ≫ a = 0) :
    koszulExactTopExtCoefficientRestrictionEquiv n H he N
      (tildeKoszulIsoCocycleModuleExt R H he (n+1) N lambda a ha) =
      Submodule.Quotient.mk ((tildeActualFunctionalPreimage R
        (tildeKoszulIsoCocycle R H (n+1) N lambda a)).hom (topKoszulGenerator (n+1))) :=
  tildeActualCocycleModuleExt_topRestriction R n H he N _
    (tildeKoszulIsoCocycle_isCocycle R H (n+1) N lambda a ha)

end LinearStudy
