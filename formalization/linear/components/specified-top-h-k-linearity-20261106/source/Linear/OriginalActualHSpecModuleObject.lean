module
public import Linear.OriginalActualHBaseModuleObject
public import Linear.ProjectiveCanonicalCoefficientEquiv
public import Linear.SchemeModuleActualHSpecScalars
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The canonical coordinate coefficient map is precisely the map
used in the original actual-H scalar restriction. -/
theorem coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv (K : Type) [CommRing K] :
    (MvPolynomial.coordinateCanonicalCoefficientRingEquiv K).toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl

/-- The original independently defined K-module on actual H. -/
def originalActualHSpecModuleObject
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ) : ModuleCat.{u} K :=
  @ModuleCat.of K _ (schemeModuleActualCohomology X M n)
    (schemeModuleActualCohomologyAddCommGroup X M n)
    (schemeModuleActualHSpecModule pi M n)

/-- Restricting the independently defined Γ-module along the
canonical coefficient map gives the original K-module object. -/
theorem originalActualHSpecModuleObject_eq_restrictScalars
    {K : Type u} [CommRing K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (n : ℕ) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).obj
      (originalActualHBaseModuleObject pi M n) =
    originalActualHSpecModuleObject pi M n := rfl

end LinearStudy
#check LinearStudy.coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv
#print axioms LinearStudy.coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv
#check LinearStudy.originalActualHSpecModuleObject
#print axioms LinearStudy.originalActualHSpecModuleObject
#check LinearStudy.originalActualHSpecModuleObject_eq_restrictScalars
#print axioms LinearStudy.originalActualHSpecModuleObject_eq_restrictScalars
