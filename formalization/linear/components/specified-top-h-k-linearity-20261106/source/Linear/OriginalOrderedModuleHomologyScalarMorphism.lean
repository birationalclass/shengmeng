module
/- UNCOMPILED next-window candidate. No verified result is claimed. -/
public import Linear.OriginalModuleCatScalarMorphism
public import Linear.OrderedModuleCechActualCoefficientMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
/-- Use the original homology scalar theorem categorically, without
applying the large original Cech-homology object to an element. -/
theorem originalOrderedModuleHomologyScalarMorphism
    {X S : Scheme.{u}} (pi : X ⟶ S) (M : X.Modules) (r : Γ(S,⊤))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap (orderedBaseCechActualCoefficientMap pi
        (originalGlobalModuleScalar (pi.appTop r) M) U) n) =
      ((orderedBaseCechComplex pi M U).homology n).smul r := by
  let C := (orderedBaseCechComplex pi M U).homology n
  let F := forget₂ (ModuleCat.{u} Γ(S,⊤)) AddCommGrpCat.{u}
  have h : HomologicalComplex.homologyMap
      (orderedBaseCechActualCoefficientMap pi (originalGlobalModuleScalar (pi.appTop r) M) U) n =
        r • 𝟙 C := orderedBaseCech_homologyMap_originalScalar pi M r U n
  exact (congrArg (fun f : C ⟶ C => F.map f) h).trans
    (originalModuleScalarMorphism_eq_forget_smul_id C r).symm
end LinearStudy
#check LinearStudy.originalOrderedModuleHomologyScalarMorphism
#print axioms LinearStudy.originalOrderedModuleHomologyScalarMorphism
