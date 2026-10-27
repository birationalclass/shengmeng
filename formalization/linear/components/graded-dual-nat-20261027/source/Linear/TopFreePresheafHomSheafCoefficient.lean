module
public import Linear.TopOpenFreeAbelianHomPresheaf
public import Mathlib.CategoryTheory.Adjunction.Additive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u v v'
namespace LinearStudy
/-- The native additive adjunction identifies actual Hom presheaves,in a shared Hom
universe,without changing the coefficient object or introducing a comparison premise. -/
def nativeAdjunctionHomPresheafIso
    {A : Type v} [Category.{u} A] [Preadditive A]
    {B : Type v'} [Category.{u} B] [Preadditive B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [L.Additive] [R.Additive] (N : B) :
    L.op ⋙ preadditiveYoneda.obj N ≅ preadditiveYoneda.obj (R.obj N) :=
  NatIso.ofComponents (fun V => (adj.homAddEquiv V.unop N).toAddCommGrpIso)
    (fun f => by ext a; exact adj.homEquiv_naturality_left f.unop a)

/-- The ORIGINAL free-open abelian presheaf,with actual sheaf coefficient F,
corepresents the SAME sections naturally in all open inclusions. -/
def topOpenFreeAbelianPresheafHomPresheafIso (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (topOpenFreeAbelianPresheafFunctor X).op ⋙ preadditiveYoneda.obj F.obj ≅ F.obj := by
  let K := topOpenFreeAbelianPresheafFunctor X
  let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let Y := preadditiveYoneda.obj F
  let e := nativeAdjunctionHomPresheafIso
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F
  exact Functor.isoWhiskerLeft K.op e.symm ≪≫
    (Functor.associator K.op S.op Y).symm ≪≫
    Functor.isoWhiskerRight (Functor.opComp K S).symm Y ≪≫
    topOpenFreeAbelianSheafHomPresheafIso X F
end LinearStudy
