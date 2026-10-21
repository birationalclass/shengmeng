module
public import Linear.OverOpenUnitZeroSheafAdjoint
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {C : Type u} [Preorder C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An actual local morphism from the unit into an injective extends globally. -/
theorem overOpenUnitHom_extend_of_injective (I : SheafOfModules.{u} R) [Injective I]
    (a : SheafOfModules.unit (R.over U) ⟶ (SheafOfModules.overFunctor R U).obj I) :
    ∃ b : SheafOfModules.unit R ⟶ I, (SheafOfModules.overFunctor R U).map b = a := by
  let adj := overOpenZeroSheafAdjunction R U
  let c := (adj.homEquiv _ I).symm a
  let j := overOpenUnitZeroSheafToUnit R U
  letI : Mono j := overOpenUnitZeroSheafToUnit_mono R U
  let b := Injective.factorThru c j
  refine ⟨b, ?_⟩
  have h : j ≫ b = c := Injective.comp_factorThru c j
  have hc := congrArg (adj.homEquiv _ I) h
  have hn := adj.homEquiv_naturality_right j b
  have hj : adj.homEquiv _ (SheafOfModules.unit R) j = 𝟙 _ :=
    overOpenUnitZeroSheafToUnit_adjoint R U
  exact (Category.id_comp _).symm.trans
    ((congrArg (fun z => z ≫ (SheafOfModules.overFunctor R U).map b) hj).symm.trans
      (hn.symm.trans (hc.trans ((adj.homEquiv _ I).apply_symm_apply a))))
end LinearStudy
