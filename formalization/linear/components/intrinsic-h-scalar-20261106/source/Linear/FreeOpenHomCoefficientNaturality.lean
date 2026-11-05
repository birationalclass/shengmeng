module
public import Linear.TopFreePresheafHomSheafCoefficient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u v v'
/-- Native additive adjunction Hom-presheaf comparison is natural in
actual coefficients,by the existing adjunction naturality law. -/
theorem nativeAdjunctionHomPresheafIso_coefficient_naturality
    {A : Type v} [Category.{u} A] [Preadditive A]
    {B : Type v'} [Category.{u} B] [Preadditive B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [L.Additive] [R.Additive]
    {F G : B} (a : F ⟶ G) :
    Functor.whiskerLeft L.op (preadditiveYoneda.map a) ≫
      (nativeAdjunctionHomPresheafIso adj G).hom =
      (nativeAdjunctionHomPresheafIso adj F).hom ≫ preadditiveYoneda.map (R.map a) := by
  ext P b
  exact adj.homEquiv_naturality_right b a
/-- SAME original free-open sheaf/section Hom comparison is natural
in original sheaf coefficients;actual section morphism retained. -/
theorem topOpenFreeAbelianSheafHomPresheafIso_coefficient_naturality
    (X : TopCat.{u}) {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) :
    Functor.whiskerLeft (topOpenFreeAbelianSheafFunctor X).op (preadditiveYoneda.map a) ≫
      (topOpenFreeAbelianSheafHomPresheafIso X G).hom =
      (topOpenFreeAbelianSheafHomPresheafIso X F).hom ≫ a.hom := by
  ext U b
  exact topOpenFreeAbelianSheafHomEquiv_postcompose X U.unop a b
/-- SAME original free-open PRESHEAF Hom/section comparison is natural
in sheaf coefficients;sheafification adjunction inverse is calibrated. -/
theorem topOpenFreeAbelianPresheafHomPresheafIso_coefficient_naturality
    (X : TopCat.{u}) {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) :
    Functor.whiskerLeft (topOpenFreeAbelianPresheafFunctor X).op (preadditiveYoneda.map a.hom) ≫
      (topOpenFreeAbelianPresheafHomPresheafIso X G).hom =
      (topOpenFreeAbelianPresheafHomPresheafIso X F).hom ≫ a.hom := by
  ext U b
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  change topOpenFreeAbelianSheafHomEquiv X U.unop G
      ((adj.homEquiv ((topOpenFreeAbelianPresheafFunctor X).obj U.unop) G).symm (b ≫ a.hom)) =
    a.hom.app U (topOpenFreeAbelianSheafHomEquiv X U.unop F
      ((adj.homEquiv ((topOpenFreeAbelianPresheafFunctor X).obj U.unop) F).symm b))
  exact (congrArg (topOpenFreeAbelianSheafHomEquiv X U.unop G)
    (adj.homEquiv_naturality_right_symm b a)).trans
      (topOpenFreeAbelianSheafHomEquiv_postcompose X U.unop a _)
end LinearStudy
