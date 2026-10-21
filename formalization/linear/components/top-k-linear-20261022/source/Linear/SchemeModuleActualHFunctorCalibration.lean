module
public import Linear.SchemeModuleActualHScalarRingHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
/-- A small exact interface to native actual H.map;the same coefficient
map and native cohomology group are retained definitionally. -/
theorem schemeModuleActualHFunctor_map_apply (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : schemeModuleActualCohomology X M n) :
    (schemeModuleActualHFunctor X n).map f x =
      CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n x := rfl
/-- The intrinsic scalar ring action is exactly the native H functor on
actual scalar multiplication;no comparison equivalence is used. -/
theorem schemeModuleActualHScalarRingHom_applyFunctor (X : Scheme.{u})
    (M : X.Modules) (n : ℕ) (r : Γ(X,⊤)) (x : schemeModuleActualCohomology X M n) :
    schemeModuleActualHScalarRingHom X M n r x =
      (schemeModuleActualHFunctor X n).map (originalGlobalModuleScalar r M) x := rfl
end LinearStudy
