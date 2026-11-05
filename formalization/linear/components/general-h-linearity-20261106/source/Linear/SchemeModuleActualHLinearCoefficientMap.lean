module
public import Linear.SchemeModuleActualHGlobalSectionsModule
public import Linear.SchemeModuleActualHFunctorCalibration
public import Linear.AdditiveFunctorScalarSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
/-- The native coefficient map commutes with the INTRINSIC action of the
same original global section,in EVERY degree. Derived from the original
module-map scalar square through the SAME native H functor. -/
theorem schemeModuleActualH_scalar_naturality (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ) (r : Γ(X,⊤))
    (x : schemeModuleActualCohomology X M n) :
    CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n
        (schemeModuleActualHScalarRingHom X M n r x) =
      schemeModuleActualHScalarRingHom X N n r
        (CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n x) := by
  rw [schemeModuleActualHScalarRingHom_applyFunctor X M n,
    schemeModuleActualHScalarRingHom_applyFunctor X N n,
    ← schemeModuleActualHFunctor_map_apply X f n,
    ← schemeModuleActualHFunctor_map_apply X f n]
  exact additiveFunctor_map_commuting_apply (schemeModuleActualHFunctor X n) f
    (originalGlobalModuleScalar r M) (originalGlobalModuleScalar r N)
    (originalGlobalModuleScalar_naturality r f) x
/-- The SAME original native-H coefficient map is linear for intrinsic
ORIGINAL-global-section module structures. No comparison choice is used. -/
def schemeModuleActualHLinearCoefficientMap (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    letI := schemeModuleActualHGlobalSectionsModule X M n
    letI := schemeModuleActualHGlobalSectionsModule X N n
    schemeModuleActualCohomology X M n →ₗ[Γ(X,⊤)] schemeModuleActualCohomology X N n := by
  letI := schemeModuleActualHGlobalSectionsModule X M n
  letI := schemeModuleActualHGlobalSectionsModule X N n
  exact {
    __ := CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n
    map_smul' := fun r x => schemeModuleActualH_scalar_naturality X f n r x }
/-- Exact underlying map,not a transported substitute. -/
theorem schemeModuleActualHLinearCoefficientMap_apply (X : Scheme.{u})
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : schemeModuleActualCohomology X M n) :
    schemeModuleActualHLinearCoefficientMap X f n x =
      CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n x := rfl
end LinearStudy
