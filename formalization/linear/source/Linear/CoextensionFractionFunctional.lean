module
public import Linear.FiniteCoextensionModule
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The native restricted coextension dual is the ordinary dual of
the original algebra carrier, via two actual scalar comparisons. -/
def coextensionOriginalDualEquiv :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[R]
      Module.Dual R S :=
  restrictedCoextensionDualEquiv.trans (Module.Dual.congr restrictedAlgebraModuleEquiv)

/-- Extend the original functional to the actual fraction fields through
their proved localization structures. The extension is not assumed. -/
def coextensionFractionFunctional
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    Module.Dual (FractionRing R) (FractionRing S) :=
  IsLocalizedModule.mapExtendScalars (nonZeroDivisors R)
    (IsScalarTower.toAlgHom R S (FractionRing S)).toLinearMap
    (Algebra.linearMap R (FractionRing R)) (FractionRing R)
      (coextensionOriginalDualEquiv (R := R) (S := S) ell)

/-- The extended functional retains the values of the original one on
the actual original algebra, embedded into the base fraction field. -/
theorem coextensionFractionFunctional_apply_original
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) (x : S) :
    coextensionFractionFunctional ell (algebraMap S (FractionRing S) x) =
      algebraMap R (FractionRing R) (ell x) := by
  change (IsLocalizedModule.map (nonZeroDivisors R)
    (IsScalarTower.toAlgHom R S (FractionRing S)).toLinearMap
    (Algebra.linearMap R (FractionRing R))
      (coextensionOriginalDualEquiv (R := R) (S := S) ell))
        ((IsScalarTower.toAlgHom R S (FractionRing S)).toLinearMap x) = _
  rw [IsLocalizedModule.map_apply]
  rfl

/-- The actual extension map does not lose a nonzero original dual
functional: injectivity follows by restricting back to original elements. -/
theorem coextensionFractionFunctional_injective :
    Function.Injective (coextensionFractionFunctional (R := R) (S := S)) := by
  intro a b hab
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro x
  apply IsFractionRing.injective R (FractionRing R)
  have h := congrArg (fun f => f (algebraMap S (FractionRing S) (x : S))) hab
  simpa only [coextensionFractionFunctional_apply_original] using h

end LinearStudy
