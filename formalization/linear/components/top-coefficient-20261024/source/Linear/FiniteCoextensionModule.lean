module
public import Linear.ExtendScalarsActualTensor
public import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual restricted coextension dual agrees with the usual R-linear
dual. Both scalar actions are compared, rather than assumed equal. -/
def restrictedCoextensionDualEquiv :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) →ₗ[R] R) where
  toFun := fun ell => ModuleCat.CoextendScalars.equiv (algebraMap R S) (ModuleCat.of R R) ell
  invFun := fun ell => (ModuleCat.CoextendScalars.equiv (algebraMap R S)
    (ModuleCat.of R R)).symm ell
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro a ell
    apply LinearMap.ext
    intro x
    let ell' : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) := ell
    let l := ModuleCat.CoextendScalars.equiv (algebraMap R S) (ModuleCat.of R R) ell'
    let z : S := x
    let w : S := z * algebraMap R S a
    change l w = a * l x
    have hx : (w : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) =
        (a • x : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) := by
      simp only [w,z,ModuleCat.restrictScalars.smul_def,smul_eq_mul,mul_comm]
    rw [hx]
    exact l.map_smul a x

/-- The actual coextension dual is finite over the normalization base,
without a freeness or Cohen--Macaulay assumption. -/
theorem restrictedCoextensionDual_finite [IsNoetherianRing R] [Module.Finite R S] :
    Module.Finite R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) := by
  letI : Module.Finite R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) := Module.Finite.equiv restrictedAlgebraModuleEquiv.symm
  exact Module.Finite.equiv (restrictedCoextensionDualEquiv (R := R) (S := S)).symm

end LinearStudy
