module
public import Linear.OriginalScalarSquareModuleIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v

/-- Lift the original additive comparison with the target operator
presented as a literal morphism of additive groups. -/
def originalScalarSquareModuleIso_literal
    {R : Type u} [Ring R] (C G : ModuleCat.{v} R) {Y : AddCommGrpCat.{v}}
    (I : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C ≅ Y)
    (e : Y = (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj G)
    (a : R → End ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C))
    (d : R → (Y ⟶ Y))
    (ha : ∀ r, a r = C.smul r) (hd : ∀ r, HEq (d r) (G.smul r))
    (w : ∀ r, (a r).asHom ≫ I.hom = I.hom ≫ d r) :
    C ≅ G :=
  originalScalarSquareModuleIso C G I e a (fun r => End.of (d r)) ha hd w

theorem originalScalarSquareModuleIso_literal_forget_hom
    {R : Type u} [Ring R] (C G : ModuleCat.{v} R) {Y : AddCommGrpCat.{v}}
    (I : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C ≅ Y)
    (e : Y = (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj G)
    (a : R → End ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C))
    (d : R → (Y ⟶ Y))
    (ha : ∀ r, a r = C.smul r) (hd : ∀ r, HEq (d r) (G.smul r))
    (w : ∀ r, (a r).asHom ≫ I.hom = I.hom ≫ d r) :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map
      (originalScalarSquareModuleIso_literal C G I e a d ha hd w).hom ≫ eqToHom e.symm =
      I.hom :=
  originalScalarSquareModuleIso_forget_hom C G I e a (fun r => End.of (d r)) ha hd w

end LinearStudy
#check LinearStudy.originalScalarSquareModuleIso_literal
#print axioms LinearStudy.originalScalarSquareModuleIso_literal
#check LinearStudy.originalScalarSquareModuleIso_literal_forget_hom
#print axioms LinearStudy.originalScalarSquareModuleIso_literal_forget_hom
