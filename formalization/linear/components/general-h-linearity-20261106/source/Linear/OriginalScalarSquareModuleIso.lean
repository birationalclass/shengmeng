module
public import Linear.CategoricalScalarSquareComposition
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.EqToHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory
universe u v

/-- Lift a fixed additive comparison using the independently given
source and target scalar actions. The target change is the supplied
equality of additive group objects. -/
def originalScalarSquareModuleIso
    {R : Type u} [Ring R] (C G : ModuleCat.{v} R) {Y : AddCommGrpCat.{v}}
    (I : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C ≅ Y)
    (e : Y = (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj G)
    (a : R → End ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C))
    (d : R → End Y)
    (ha : ∀ r, a r = C.smul r) (hd : ∀ r, HEq (d r).asHom (G.smul r).asHom)
    (w : ∀ r, (a r).asHom ≫ I.hom = I.hom ≫ (d r).asHom) :
    C ≅ G :=
  ModuleCat.isoMk (I ≪≫ eqToIso e) (fun r => by
    have h₁ := (congrArg (fun g => g ≫ I.hom) (ha r).symm).trans (w r)
    have h₂ : (d r).asHom ≫ eqToHom e = eqToHom e ≫ (G.smul r).asHom :=
      eq_of_heq ((comp_eqToHom_heq (d r).asHom e).trans
        ((hd r).trans (eqToHom_comp_heq (G.smul r).asHom e).symm))
    exact (originalEndomorphismSquare_comp h₁ h₂).symm)

/-- After identifying the exact target group, the lifted isomorphism
has the original comparison morphism. -/
theorem originalScalarSquareModuleIso_forget_hom
    {R : Type u} [Ring R] (C G : ModuleCat.{v} R) {Y : AddCommGrpCat.{v}}
    (I : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C ≅ Y)
    (e : Y = (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj G)
    (a : R → End ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj C))
    (d : R → End Y)
    (ha : ∀ r, a r = C.smul r) (hd : ∀ r, HEq (d r).asHom (G.smul r).asHom)
    (w : ∀ r, (a r).asHom ≫ I.hom = I.hom ≫ (d r).asHom) :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map
      (originalScalarSquareModuleIso C G I e a d ha hd w).hom ≫ eqToHom e.symm = I.hom := by
  rw [originalScalarSquareModuleIso, ModuleCat.isoMk_hom, ModuleCat.forget₂_map_homMk, Iso.trans_hom]
  simp [Category.assoc]

end LinearStudy
#check LinearStudy.originalScalarSquareModuleIso
#print axioms LinearStudy.originalScalarSquareModuleIso
#check LinearStudy.originalScalarSquareModuleIso_forget_hom
#print axioms LinearStudy.originalScalarSquareModuleIso_forget_hom
