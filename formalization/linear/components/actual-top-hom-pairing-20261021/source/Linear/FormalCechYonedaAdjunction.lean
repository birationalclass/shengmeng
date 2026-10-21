/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module
public import Linear.FormalCoproductFunctorMap
public import Linear.CoverGeneratedTerminalPresheaf

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Subfunctor.Sieves
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Native presheaf Cech augmentation and its actual quasi-isomorphism

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
/- Minimal inspected adaptation of Joel Riou mathlib4,commit04b574a2dc239b7964d235d5f66e31c37162b449. Apache2.0. Native objects retained;private continuation,NOT a completed Cech/native-H comparison. -/


universe w t v v' v'' u u' u''

open AlgebraicTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

open Opposite Limits

-- to be moved
noncomputable def isTerminalShrinkYonedaObj [LocallySmall.{w} C]
    {T : C} (hT : IsTerminal T) :
    IsTerminal (shrinkYoneda.{w}.obj T) :=
  Functor.isTerminal (fun _ ↦ (Types.isTerminalEquivUnique _).2
    { default := shrinkYonedaObjObjEquiv.symm (hT.from _)
      uniq _ := shrinkYonedaObjObjEquiv.injective (hT.hom_ext _ _)})

namespace Subfunctor

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {ι : Type*} (U : ι → C)

-- to be moved
def ofObjectsIsoOfAdj :
    F.op ⋙ (ofObjects U).toFunctor ≅
      (ofObjects (G.obj ∘ U)).toFunctor :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso ((Equiv.refl _).subtypeEquiv (fun _ ↦ by
    simp only [Functor.op_obj, Functor.const_obj_obj, ofObjects, Set.mem_ofPred_eq,
      Function.comp_apply, Equiv.refl_apply]
    constructor
    · rintro ⟨i, ⟨f⟩⟩
      exact ⟨i, ⟨adj.homEquiv _ _ f⟩⟩
    · rintro ⟨i, ⟨f⟩⟩
      exact ⟨i, ⟨(adj.homEquiv _ _).symm f⟩⟩))) (fun _ ↦ rfl)

end Subfunctor

namespace Adjunction

variable [LocallySmall.{w} C] [LocallySmall.{w} D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)

noncomputable def shrinkYonedaIso :
    (shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj F.op) ≅
      G ⋙ shrinkYoneda.{w} :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ Equiv.toIso (
        shrinkYonedaObjObjEquiv.trans ((adj.homEquiv Y.unop X).trans
          shrinkYonedaObjObjEquiv.symm))) (fun f ↦ by
            ext g
            obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
            dsimp
            simp only [Equiv.toIso_hom_hom_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
            simp only [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm]
            have hn0 := shrinkYonedaObjObjEquiv_obj_map ((F.map f.unop).op)
              (shrinkYonedaObjObjEquiv.symm g)
            have hn := hn0.trans
              (congrArg (fun z => F.map f.unop ≫ z) (shrinkYonedaObjObjEquiv.apply_symm_apply g))
            exact (congrArg (fun z => shrinkYonedaObjObjEquiv.symm (adj.homEquiv _ _ z)) hn).trans
              (congrArg shrinkYonedaObjObjEquiv.symm (adj.homEquiv_naturality_left f.unop g)))) (fun f ↦ by
            ext _ g
            obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
            dsimp
            simp only [Equiv.toIso_hom_hom_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
            simp only [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
            have hn0 := shrinkYonedaObjObjEquiv_map_app (shrinkYonedaObjObjEquiv.symm g) f
            have hn := hn0.trans
              (congrArg (fun z => z ≫ f) (shrinkYonedaObjObjEquiv.apply_symm_apply g))
            exact (congrArg (fun z => shrinkYonedaObjObjEquiv.symm (adj.homEquiv _ _ z)) hn).trans
              (congrArg shrinkYonedaObjObjEquiv.symm (adj.homEquiv_naturality_right g f)))

end Adjunction

end CategoryTheory
