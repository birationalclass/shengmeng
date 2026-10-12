module
public import Linear.CoextensionFractionFunctional
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

/-- The actual fraction-field extension of dual functionals intertwines
the native upper-ring action with multiplication in the actual fraction field. -/
theorem coextensionFractionFunctional_smul
    (b : S) (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    coextensionFractionFunctional (b • ell) =
      (coextensionFractionFunctional ell).comp
        (LinearMap.mulRight (FractionRing R) (algebraMap S (FractionRing S) b)) := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (nonZeroDivisors R)
    (IsScalarTower.toAlgHom R S (FractionRing S)).toLinearMap
    (Algebra.linearMap R (FractionRing R))
  ext x
  simp only [LinearMap.coe_restrictScalars,LinearMap.comp_apply,
    LinearMap.mulRight_apply,IsScalarTower.toAlgHom_apply]
  change coextensionFractionFunctional (b • ell) (algebraMap S (FractionRing S) x) =
    coextensionFractionFunctional ell
      (algebraMap S (FractionRing S) x * algebraMap S (FractionRing S) b)
  rw [coextensionFractionFunctional_apply_original,← map_mul,
    coextensionFractionFunctional_apply_original]
  rfl

/-- Rebundle the constructed ordinary generic functional into the actual
native coextension dual of the original fraction-field extension. -/
def coextensionFractionNative
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    (ModuleCat.coextendScalars (algebraMap (FractionRing R) (FractionRing S))).obj
      (ModuleCat.of (FractionRing R) (FractionRing R)) :=
  (coextensionOriginalDualEquiv (R := FractionRing R) (S := FractionRing S)).symm
    (coextensionFractionFunctional ell)

/-- This is an actual upper-ring linear map, not only an injective map of sets. -/
def coextensionFractionNativeLinear :
    (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) →ₗ[S]
      (ModuleCat.restrictScalars (algebraMap S (FractionRing S))).obj
        ((ModuleCat.coextendScalars (algebraMap (FractionRing R) (FractionRing S))).obj
          (ModuleCat.of (FractionRing R) (FractionRing R))) where
  toFun := coextensionFractionNative
  map_add' := by
    intro a b
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    change coextensionFractionFunctional (a+b) (x : FractionRing S) =
      coextensionFractionFunctional a (x : FractionRing S) +
      coextensionFractionFunctional b (x : FractionRing S)
    simp only [coextensionFractionFunctional,LinearEquiv.map_add,LinearMap.map_add,
      LinearMap.add_apply]
  map_smul' := by
    intro b ell
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    let z : FractionRing S := x
    let w : FractionRing S := z * algebraMap S (FractionRing S) b
    change coextensionFractionFunctional (b • ell) z = coextensionFractionFunctional ell w
    rw [coextensionFractionFunctional_smul]
    rfl

theorem coextensionFractionNativeLinear_injective :
    Function.Injective (coextensionFractionNativeLinear (R := R) (S := S)) := by
  intro a b h
  apply coextensionFractionFunctional_injective
  change (coextensionOriginalDualEquiv (R := FractionRing R) (S := FractionRing S)).symm
      (coextensionFractionFunctional a) =
    (coextensionOriginalDualEquiv (R := FractionRing R) (S := FractionRing S)).symm
      (coextensionFractionFunctional b) at h
  exact (coextensionOriginalDualEquiv (R := FractionRing R) (S := FractionRing S)).symm.injective h

end LinearStudy
