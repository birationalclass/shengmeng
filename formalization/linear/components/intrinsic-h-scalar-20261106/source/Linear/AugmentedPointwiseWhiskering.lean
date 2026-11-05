module
public import Linear.AugmentedAlternatingWhiskering
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits
universe u v u' v' w
namespace LinearStudy
set_option backward.defeqAttrib.useBackward true in
/-- Applying a functor to presheaves and then evaluating is the same actual
augmented simplicial object as evaluating first and applying that functor. -/
def augmentedPointwiseWhiskeringIso
    {C : Type u} [Category.{v} C]
    {A : Type u'} [Category.{v'} A]
    (S : SimplicialObject.Augmented (C ⥤ Type w)) (G : Type w ⥤ A) (X : C) :
    (((SimplicialObject.Augmented.whiskering (C ⥤ A) A).obj
      ((evaluation C A).obj X)).obj
      (((SimplicialObject.Augmented.whiskering _ _).obj
        ((Functor.whiskeringRight C (Type w) A).obj G)).obj S)) ≅
    (((SimplicialObject.Augmented.whiskering (Type w) A).obj G).obj
      (((SimplicialObject.Augmented.whiskering _ _).obj
        ((evaluation C (Type w)).obj X)).obj S)) := by
  refine Comma.isoMk (Iso.refl _) (Iso.refl _) ?_
  ext n
  simp [SimplicialObject.Augmented.whiskering,SimplicialObject.Augmented.whiskeringObj]
end LinearStudy
