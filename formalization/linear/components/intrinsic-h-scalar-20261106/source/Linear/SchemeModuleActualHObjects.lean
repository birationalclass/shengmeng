module
public import Linear.SchemeModuleFiniteSupportCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- A named interface for the EXACT original actual-H group object.
No new cohomology group,transported action or mathematical input. -/
def schemeModuleActualHObject (X : Scheme.{u}) (M : X.Modules) (n : ℕ) : AddCommGrpCat.{u} :=
  (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology X) n).obj
    ((schemeModuleToActualAbelianSheaf X).obj M)
/-- The EXACT original actual-H coefficient morphism,with cached objects. -/
def schemeModuleActualHCoefficientHom {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    schemeModuleActualHObject X M n ⟶ schemeModuleActualHObject X N n :=
  (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology X) n).map
    ((schemeModuleToActualAbelianSheaf X).map f)
theorem schemeModuleActualHObject_eq_original (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    schemeModuleActualHObject X M n =
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology X) n).obj
        ((schemeModuleToActualAbelianSheaf X).obj M) := rfl
theorem schemeModuleActualHObject_carrier_eq_original (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    (schemeModuleActualHObject X M n : Type u) = schemeModuleActualCohomology X M n := rfl
theorem schemeModuleActualHCoefficientHom_eq_original {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    schemeModuleActualHCoefficientHom f n =
      (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology X) n).map
        ((schemeModuleToActualAbelianSheaf X).map f) := rfl
end LinearStudy
