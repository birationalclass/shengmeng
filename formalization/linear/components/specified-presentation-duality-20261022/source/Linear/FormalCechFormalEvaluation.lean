/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module
public import Linear.FormalCechYonedaAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
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
namespace Limits.FormalCoproduct

variable {E : Type u''} [Category.{v''} E]

noncomputable def evalObjCompIso [HasCoproducts.{w} D] [HasCoproducts.{w} E] (F : C ⥤ D)
    (G : D ⥤ E)
    [∀ (α : Type w), PreservesColimitsOfShape (Discrete α) G] :
    (eval.{w} C E).obj (F ⋙ G) ≅
      (eval.{w} C D).obj F ⋙ G :=
  NatIso.ofComponents (fun _ ↦ (PreservesCoproduct.iso G _).symm) (fun {U V} f ↦ by
    dsimp [eval]
    apply Sigma.hom_ext
    intro i
    simpa [Function.comp_def, -ι_comp_sigmaComparison] using
      G.map (F.map (f.φ i)) ≫= ι_comp_sigmaComparison G (F.obj ∘ V.obj) (f.f i))

variable [LocallySmall.{w} C] [LocallySmall.{w} D]

open Functor

section

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)

noncomputable def evalShrinkYonedaCompIsoOfAdj :
    (eval C _).obj shrinkYoneda.{w} ⋙ (whiskeringLeft _ _ _).obj F.op ≅
      G.mapFormalCoproduct ⋙ (eval _ _).obj shrinkYoneda :=
  (evalObjCompIso _ _).symm ≪≫ (eval C _).mapIso adj.shrinkYonedaIso

end

end Limits.FormalCoproduct
end CategoryTheory
