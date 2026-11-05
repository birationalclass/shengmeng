module
public import Linear.OriginalActualHBaseModuleObject
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u

/-- On the original actual H group, the original base scalar morphism
has exactly the underlying additive map of native H on the original
coefficient scalar. -/
theorem originalActualHBaseScalarRawMorphism
    {X S : Scheme.{u}} (pi : X ⟶ S) (M : X.Modules) (n : ℕ) (r : Γ(S,⊤)) :
    (originalActualHBaseModuleObject pi M n).smul r =
      @AddCommGrpCat.ofHom (schemeModuleActualCohomology X M n)
        (schemeModuleActualCohomology X M n)
        (schemeModuleActualCohomologyAddCommGroup X M n)
        (schemeModuleActualCohomologyAddCommGroup X M n)
        (CategoryTheory.Sheaf.H.map.{u}
        ((schemeModuleToActualAbelianSheaf X).map
          (originalGlobalModuleScalar (pi.appTop r) M)) n) := by
  apply AddCommGrpCat.ext
  intro x
  exact schemeModuleActualHBaseModule_smul pi M n r x

end LinearStudy
#check LinearStudy.originalActualHBaseScalarRawMorphism
#print axioms LinearStudy.originalActualHBaseScalarRawMorphism
