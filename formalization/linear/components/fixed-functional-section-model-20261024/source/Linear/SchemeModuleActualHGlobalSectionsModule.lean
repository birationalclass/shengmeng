module
public import Linear.SchemeModuleActualHScalarRingHom
public import Mathlib.Algebra.Module.RingHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
/-- Native actual H is a module over ORIGINAL global structure sections,
using ONLY the intrinsic original-coefficient-multiplication ring action.
The existing additive group and actual sheaf cohomology are unchanged. -/
def schemeModuleActualHGlobalSectionsModule (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    Module Γ(X,⊤) (schemeModuleActualCohomology X M n) :=
  Module.compHom (schemeModuleActualCohomology X M n) (schemeModuleActualHScalarRingHom X M n)
/-- EXACT action formula in every degree;no scalar-compatibility assumption
and no scalar action transported through a duality comparison. -/
theorem schemeModuleActualHGlobalSectionsModule_smul
    (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (r : Γ(X,⊤)) (x : schemeModuleActualCohomology X M n) :
    letI := schemeModuleActualHGlobalSectionsModule X M n
    r • x = CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
      (originalGlobalModuleScalar r M)) n x := rfl
end LinearStudy
