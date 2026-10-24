module
public import Linear.SchemeModuleActualHBaseScalars
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u
/-- Intrinsic coefficient-ring action on actual H over Spec K. Restrict
along the CANONICAL GammaSpecIso inverse;no cohomology comparison is used. -/
def schemeModuleActualHSpecModule {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ) :
    Module K (schemeModuleActualCohomology X M n) := by
  letI := schemeModuleActualHBaseModule pi M n
  exact Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
/-- Exact ORIGINAL coefficient multiplication formula,in every degree. -/
theorem schemeModuleActualHSpecModule_smul {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ)
    (r : K) (x : schemeModuleActualCohomology X M n) :
    letI := schemeModuleActualHSpecModule pi M n
    r • x = CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map
      (originalGlobalModuleScalar (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) M)) n x := rfl
/-- ORIGINAL actual-H coefficient maps are K-linear for this intrinsic action. -/
def schemeModuleActualHSpecLinearCoefficientMap {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    letI := schemeModuleActualHSpecModule pi M n
    letI := schemeModuleActualHSpecModule pi N n
    schemeModuleActualCohomology X M n →ₗ[K] schemeModuleActualCohomology X N n := by
  letI := schemeModuleActualHSpecModule pi M n
  letI := schemeModuleActualHSpecModule pi N n
  exact {
    __ := CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n
    map_smul' := fun r x => schemeModuleActualH_scalar_naturality X f n
      (pi.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) x }
/-- Underlying coefficient map is EXACTLY the pre-existing H.map. -/
theorem schemeModuleActualHSpecLinearCoefficientMap_apply {K : Type u} [CommRing K]
    {X : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K))
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ) (x : schemeModuleActualCohomology X M n) :
    schemeModuleActualHSpecLinearCoefficientMap pi f n x =
      CategoryTheory.Sheaf.H.map.{u} ((schemeModuleToActualAbelianSheaf X).map f) n x := rfl
end LinearStudy
