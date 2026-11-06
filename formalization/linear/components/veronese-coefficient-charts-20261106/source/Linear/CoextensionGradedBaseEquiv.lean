module
public import Linear.CoextensionFractionFunctional
public import Linear.GradedHomDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]

/-- The native upper-ring action restricted to the actual base field. -/
@[instance_reducible] def coextensionGradedBaseModule :
    Module K ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :=
  Module.compHom _ (algebraMap K S)

attribute [local instance] coextensionGradedBaseModule

/-- Compare the actual base-field scalar action of the native
coextension with the pointwise base-field action of the original dual. -/
def coextensionGradedBaseEquiv :
    (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) ≃ₗ[K]
      Module.Dual R S := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let X := (ModuleCat.restrictScalars (algebraMap R S)).obj D
  letI : Module K X := Module.compHom X (algebraMap K R)
  letI : IsScalarTower K R X := IsScalarTower.of_compHom K R X
  let e : X ≃ₗ[K] Module.Dual R S :=
    (coextensionOriginalDualEquiv (R := R) (S := S)).restrictScalars K
  let c : D ≃ₗ[K] X :=
    { toFun := fun ell => ell
      invFun := fun ell => ell
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a ell
        change algebraMap K S a • ell = algebraMap R S (algebraMap K R a) • ell
        rw [IsScalarTower.algebraMap_apply K R S] }
  exact c.trans e

end LinearStudy
