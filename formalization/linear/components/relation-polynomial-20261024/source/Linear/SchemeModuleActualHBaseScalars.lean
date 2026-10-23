module
public import Linear.SchemeModuleActualHLinearCoefficientMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
/-- The ORIGINAL base-global-section action on actual H is restriction of
the intrinsic source action along the ACTUAL scheme map on global sections. -/
def schemeModuleActualHBaseModule {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (n : ℕ) : Module Γ(S,⊤) (schemeModuleActualCohomology X M n) := by
  letI := schemeModuleActualHGlobalSectionsModule X M n
  exact Module.compHom (schemeModuleActualCohomology X M n) π.appTop.hom
/-- Exact base action formula in every degree,on the SAME source space. -/
theorem schemeModuleActualHBaseModule_smul {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (n : ℕ) (r : Γ(S,⊤)) (x : schemeModuleActualCohomology X M n) :
    letI := schemeModuleActualHBaseModule π M n
    r • x = CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map
      (originalGlobalModuleScalar (π.appTop r) M)) n x := rfl
/-- The ORIGINAL actual H coefficient map is linear over the ORIGINAL
base-global-section ring,using its actual scheme structure map. -/
def schemeModuleActualHBaseLinearCoefficientMap {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    letI := schemeModuleActualHBaseModule π M n
    letI := schemeModuleActualHBaseModule π N n
    schemeModuleActualCohomology X M n →ₗ[Γ(S,⊤)] schemeModuleActualCohomology X N n := by
  letI := schemeModuleActualHBaseModule π M n
  letI := schemeModuleActualHBaseModule π N n
  exact {
    __ := CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n
    map_smul' := fun r x => schemeModuleActualH_scalar_naturality X f n (π.appTop r) x }
/-- The underlying coefficient map is EXACTLY native H.map. -/
theorem schemeModuleActualHBaseLinearCoefficientMap_apply {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ) (x : schemeModuleActualCohomology X M n) :
    schemeModuleActualHBaseLinearCoefficientMap π f n x =
      CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n x := rfl
end LinearStudy
