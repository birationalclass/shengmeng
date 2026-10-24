module
public import Linear.TopOpenFreeAbelianSheafSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Restriction is precomposition with the original open inclusion. -/
theorem topOpenFreeAbelianSheafHomEquiv_restrict (X : TopCat.{u})
    {U V : Opens X} (i : U ⟶ V) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (topOpenFreeAbelianSheafFunctor X).obj V ⟶ F) :
    topOpenFreeAbelianSheafHomEquiv X U F ((topOpenFreeAbelianSheafFunctor X).map i ≫ a) =
      F.obj.map i.op (topOpenFreeAbelianSheafHomEquiv X V F a) := by
  let adjS := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let adjA := AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ
  let b := adjS.homEquiv ((topOpenFreeAbelianPresheafFunctor X).obj V) F a
  have hS := adjS.homEquiv_naturality_left
    ((topOpenFreeAbelianPresheafFunctor X).map i) a
  have hA := adjA.homEquiv_naturality_left (uliftYoneda.{u}.map i) b
  exact (congrArg (fun g => uliftYonedaEquiv (adjA.homEquiv (uliftYoneda.{u}.obj U) F.obj g)) hS).trans
    ((congrArg uliftYonedaEquiv hA).trans (uliftYonedaEquiv_naturality _ i.op).symm)

/-- Section evaluation is natural in every original coefficient morphism. -/
theorem topOpenFreeAbelianSheafHomEquiv_postcompose (X : TopCat.{u})
    (U : Opens X) {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (a : (topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) :
    topOpenFreeAbelianSheafHomEquiv X U G (a ≫ f) =
      f.hom.app (op U) (topOpenFreeAbelianSheafHomEquiv X U F a) := by
  let adjS := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let adjA := AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ
  let b := adjS.homEquiv ((topOpenFreeAbelianPresheafFunctor X).obj U) F a
  have hS := adjS.homEquiv_naturality_right a f
  have hA := adjA.homEquiv_naturality_right b ((sheafToPresheaf _ _).map f)
  exact (congrArg (fun g => uliftYonedaEquiv (adjA.homEquiv (uliftYoneda.{u}.obj U) G.obj g)) hS).trans
    ((congrArg uliftYonedaEquiv hA).trans (uliftYonedaEquiv_comp _ _))
end LinearStudy
