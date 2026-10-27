module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.Functor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe u v u' v'
namespace LinearStudy
/-- The native alternating augmentation commutes with an actual additive functor.
This is an arrow isomorphism,with the actual single-complex comparison on its target. -/
def alternatingAugmentationWhiskeringArrowIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (S : SimplicialObject.Augmented C) (F : C ⥤ D) [F.Additive] :
    Arrow.mk ((F.mapHomologicalComplex (.down ℕ)).map
      (AlternatingFaceMapComplex.ε.app S)) ≅
    Arrow.mk (AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering C D).obj F).obj S)) := by
  refine Arrow.isoMk
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app S.left)
    ((HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).app S.right) ?_
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]
end LinearStudy
