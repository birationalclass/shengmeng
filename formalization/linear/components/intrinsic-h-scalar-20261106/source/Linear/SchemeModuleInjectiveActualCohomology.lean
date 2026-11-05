module
public import Linear.TopAbelianSheafFlasqueCohomology
public import Linear.SchemeModuleInjectiveFlasque
public import Linear.SchemeModuleGlobalExtActualHZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Every actual injective O_X-module is acyclic for the NATIVE cohomology of its underlying
abelian SHEAF;injectivity in the latter category is neither assumed nor asserted. -/
theorem schemeModule_injective_actualHigherCohomology_vanish (X : Scheme.{u})
    (I : X.Modules) [Injective I] (n : ℕ) :
    Subsingleton (schemeModuleActualCohomology X I (n+1)) :=
  topAbelianSheaf_flasque_higherCohomology_vanish X
    ((schemeModuleToActualAbelianSheaf X).obj I)
    (schemeModule_injective_isFlasque X I) n
end LinearStudy
