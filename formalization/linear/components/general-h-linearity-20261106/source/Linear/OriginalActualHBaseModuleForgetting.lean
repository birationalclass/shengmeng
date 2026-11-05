module
public import Linear.OriginalActualHBaseModuleObject
public import Linear.SchemeActualHRawObjectIdentity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u

/-- Forgetting the base scalar structure recovers the original actual H
object used by the public coefficient comparison. -/
theorem originalActualHBaseModuleObject_forget
    {X S : Scheme.{u}} (pi : X ⟶ S) (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).obj
      (originalActualHBaseModuleObject pi M n) = schemeModuleActualHObject X M n :=
  (schemeModuleActualHObject_eq_ofCohomology X M n).symm

end LinearStudy
#check LinearStudy.originalActualHBaseModuleObject_forget
#print axioms LinearStudy.originalActualHBaseModuleObject_forget
