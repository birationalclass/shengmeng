module
public import Linear.ProjectiveResolutionOriginalChainClass
public import Linear.ChainTopExtExactFunctorMappedChain
public import Linear.TildePreservesMono
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- This Prop names FORWARD exact-functor action from actual MODULE Ext
under native tilde. Its right side uses the SAME mapped chain resolution,
augmentation and functional. It is not an assertion of Ext bijectivity. -/
def tildeNativeModuleExtMappedChainLaw (R : CommRingCat.{u})
    {E M : ModuleCat.{u} R} (P : ProjectiveResolution E) (r : ℕ)
    (a : P.complex.X r ⟶ M) (ha : P.complex.d (r+1) r ≫ a = 0) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := mappedOriginalChainAugmentation_quasiIso (tilde.functor R) P.complex P.π
  (P.extMk a (r+1) rfl ha).mapExactFunctor (tilde.functor R) =
    originalChainTopExtClass (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) r
      (mappedOriginalChainAugmentation (tilde.functor R) P.complex P.π) ((tilde.functor R).map a)
      (by change (tilde.functor R).map (P.complex.d _ _) ≫ (tilde.functor R).map a = 0
          rw [← Functor.map_comp,ha,Functor.map_zero])

/-- PROVE the actual forward tilde MODULE-Ext comparison from native
mathlib extMk_hom and exact functor action. Tilde exactness is derived;
no sheaf-term projectivity,Ext-bijectivity or desired equality is assumed. -/
theorem tildeNativeModuleExtMappedChainLaw_proof (R : CommRingCat.{u})
    {E M : ModuleCat.{u} R} (P : ProjectiveResolution E) (r : ℕ)
    (a : P.complex.X r ⟶ M) (ha : P.complex.d (r+1) r ≫ a = 0) :
    tildeNativeModuleExtMappedChainLaw R P r a ha := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  change (P.extMk a (r+1) rfl ha).mapExactFunctor (tilde.functor R) = _
  rw [← originalChainTopExtClass_eq_projectiveResolution_extMk P r a ha]
  exact originalChainTopExtClass_mapExactFunctor_eq_mappedChain (tilde.functor R) P.complex r P.π a ha

end LinearStudy
