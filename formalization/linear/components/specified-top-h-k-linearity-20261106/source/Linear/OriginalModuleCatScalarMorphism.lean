module
/- UNCOMPILED next-window candidate. No verified result is claimed. -/
public import Mathlib.Algebra.Category.ModuleCat.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v
/-- Two existing presentations of the SAME native module scalar morphism. -/
theorem originalModuleScalarMorphism_eq_forget_smul_id
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (r : R) :
    M.smul r = (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map (r • 𝟙 M) := by
  apply AddCommGrpCat.ext
  intro x
  rfl
end LinearStudy
#check LinearStudy.originalModuleScalarMorphism_eq_forget_smul_id
#print axioms LinearStudy.originalModuleScalarMorphism_eq_forget_smul_id
