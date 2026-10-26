module
public import Linear.TopOpenFreeAbelianSheafAddSections
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- As an ACTUAL abelian presheaf,the Hom out of the original free-open sheaves
is the SAME coefficient sheaf's original underlying presheaf,including restrictions. -/
def topOpenFreeAbelianSheafHomPresheafIso (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (topOpenFreeAbelianSheafFunctor X).op ⋙ preadditiveYoneda.obj F ≅ F.obj :=
  NatIso.ofComponents
    (fun U => (topOpenFreeAbelianSheafHomSectionsAddEquiv X U.unop F).toAddCommGrpIso)
    (fun f => by
      ext a
      exact topOpenFreeAbelianSheafHomEquiv_restrict X f.unop F a)
end LinearStudy
