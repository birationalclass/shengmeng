module
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Sites.Limits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- ACTUAL restriction to the SAME original open,computed by native image opens. -/
def topOpenAbelianSheafRestriction (X : TopCat.{u}) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
instance topOpenAbelianSheafRestriction_additive (X : TopCat.{u}) (U : Opens X) :
    (topOpenAbelianSheafRestriction X U).Additive where
  map_add := by intros; rfl
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
instance topOpenAbelianSheafRestriction_preservesFiniteLimits (X : TopCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (topOpenAbelianSheafRestriction X U) := by
  let R := topOpenAbelianSheafRestriction X U
  let G := sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}
  haveI : G.ReflectsIsomorphisms :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{u}).reflectsIsomorphisms
  haveI : PreservesFiniteLimits G := by dsimp [G]; infer_instance
  haveI : ReflectsFiniteLimits G := reflectsFiniteLimits_of_reflectsIsomorphisms G
  haveI : PreservesFiniteLimits (R ⋙ G) := by
    change PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj U.isOpenEmbedding.functor.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves R G
instance topOpenAbelianSheafRestriction_preservesColimits (X : TopCat.{u}) (U : Opens X) :
    PreservesColimits (topOpenAbelianSheafRestriction X U) := by
  exact preservesColimits_of_natIso (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})
/-- Restriction of an ACTUAL flasque sheaf to an actual open is flasque.
No assertion that restriction preserves injectivity is needed. -/
theorem topOpenAbelianSheafRestriction_isFlasque (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : TopCat.Sheaf.IsFlasque F) :
    TopCat.Sheaf.IsFlasque ((topOpenAbelianSheafRestriction X U).obj F) := by
  constructor
  intro V W f
  exact hF.epi (U.isOpenEmbedding.functor.map f.unop).op
end LinearStudy
