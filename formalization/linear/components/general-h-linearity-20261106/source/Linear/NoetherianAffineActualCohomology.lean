module
public import Linear.NoetherianInjectiveTildeFlasque
public import Linear.TildePreservesMono
public import Linear.PointedExactFunctorExtMapIsIso
public import Linear.PointedExactFunctorExtZeroFullyFaithful
public import Linear.SchemeModuleGlobalExtActualHCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
/-- Actual affine associated sheaves preserve finite limits, using the already proved localization mono theorem. -/
@[instance] theorem tilde_functor_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := by
  letI := tilde_functor_preservesHomology R
  exact Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)

/-- On Noetherian Spec R, the native exact associated-sheaf Ext comparison from the free rank-one
module to the actual structure sheaf is bijective in EVERY degree. No vanishing input is assumed. -/
theorem noetherian_affine_tilde_globalUnitExt_comparison_bijective
    (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective (pointedExactFunctorExtMap (tilde.functor R)
      (tildeSelf (R := R)).inv M n) := by
  exact pointedExactFunctorExtMap_bijective (tilde.functor R) (tildeSelf (R := R)).inv
    (fun N => pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful
      (tilde.functor R) (tildeSelf (R := R)).inv N)
    (fun I _ j => by
      letI : Module.Injective R I := Module.injective_module_of_injective_object R I
      exact noetherian_injective_tilde_globalUnitExt_vanish R I j) M n

/-- All positive GLOBAL structure-unit Ext groups of an actual associated sheaf vanish on
Noetherian Spec R, because the source R-module is projective. This is a proved geometric result. -/
theorem noetherian_affine_tilde_globalUnitExt_vanish
    (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext.{u} (SheafOfModules.unit (Spec R).ringCatSheaf) (tilde M) (n+1)) := by
  letI : Subsingleton (Ext.{u} (ModuleCat.of R R) M (n+1)) :=
    Ext.subsingleton_of_projective (ModuleCat.of R R) M n
  have h := noetherian_affine_tilde_globalUnitExt_comparison_bijective R M (n+1)
  constructor
  intro x y
  obtain ⟨a,rfl⟩ := h.surjective x
  obtain ⟨b,rfl⟩ := h.surjective y
  exact congrArg _ (Subsingleton.elim a b)

/-- The NATIVE derived SHEAF cohomology of the SAME actual associated sheaf vanishes in ALL
positive degrees on Noetherian Spec R. No Cech/native-H or affine-acyclicity hypothesis occurs. -/
theorem noetherian_affine_tilde_actualHigherCohomology_vanish
    (R : CommRingCat.{u}) [IsNoetherianRing R] (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (schemeModuleActualCohomology (Spec R) (tilde M) (n+1)) := by
  letI := noetherian_affine_tilde_globalUnitExt_vanish R M n
  exact (schemeModuleGlobalExtActualHAddEquiv (Spec R) (tilde M) (n+1)).symm.injective.subsingleton
end LinearStudy