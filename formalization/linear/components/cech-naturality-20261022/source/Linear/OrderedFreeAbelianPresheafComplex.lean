module
public import Linear.OrderedFormalCechFunctoriality
public import Linear.TopOpenFreeAbelianSheaf
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Homology.Opposite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
/-- The actual covariant free-open presheaf formal-coproduct evaluation. -/
def orderedFreeOpenFormalPresheafFunctor (X : Scheme.{u}) :
    FormalCoproduct.{u} X.Opens ⥤ (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (FormalCoproduct.eval.{u} X.Opens (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (topOpenFreeAbelianPresheafFunctor X)
/-- Actual ordered free abelian PRESHEAF chains,with SAME original intersection
opens and integer alternating face signs.This constructs the complex only;the
augmentation quasi-isomorphism is a separate proof obligation. -/
def orderedFreeAbelianPresheafComplex (X : Scheme.{u}) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) : ChainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (orderedFormalCechComplex (orderedFreeOpenFormalPresheafFunctor X).op U).unop
end LinearStudy
