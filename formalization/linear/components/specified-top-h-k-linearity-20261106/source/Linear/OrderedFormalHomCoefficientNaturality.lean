module
public import Linear.OrderedFormalCechCoefficientFunctor
public import Linear.OrderedFormalHomCochainIso
public import Linear.ChainActualHomCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v w
/-- Actual Hom-chain source-isomorphism comparison is natural in actual
coefficients,by native mapHomologicalComplex naturality. -/
theorem actualHomSourceComplexIso_coefficient_naturality
    {A : Type w} [Category.{v} A] [Abelian A]
    {K L : ChainComplex A ℕ} (e : K ≅ L) {F G : A} (a : F ⟶ G) :
    chainActualHomCochainCoefficientMap K a ≫ (actualHomSourceComplexIso e G).hom =
      (actualHomSourceComplexIso e F).hom ≫ chainActualHomCochainCoefficientMap L a := by
  exact ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) (.up ℕ)).naturality
    (((HomologicalComplex.opFunctor A (.down ℕ)).mapIso e.symm.op).hom)).symm
/-- SAME ordered formal Hom/Cech whiskering comparison preserves actual
coefficient maps. The target is the original coefficient functor map. -/
theorem orderedFormalActualHomCochainIso_coefficient_naturality
    {X : Scheme.{u}} {A : Type w} [Category.{v} A] [Abelian A]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (P : FormalCoproduct.{u} X.Opens ⥤ A) {F G : A} (a : F ⟶ G) :
    chainActualHomCochainCoefficientMap (orderedFormalCechComplex P.op U).unop a ≫
      (orderedFormalActualHomCochainIso U P G).hom =
      (orderedFormalActualHomCochainIso U P F).hom ≫
        (orderedFormalCechCoefficientFunctor U).map (Functor.whiskerLeft P.op (preadditiveYoneda.map a)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (preadditiveYoneda.map a).app (op (P.obj (AlgebraicGeometry.Scheme.Modules.orderedCechFormalObject U n))) ≫ 𝟙 _ =
    𝟙 _ ≫ (preadditiveYoneda.map a).app (op (P.obj (AlgebraicGeometry.Scheme.Modules.orderedCechFormalObject U n)))
  simp only [Category.id_comp,Category.comp_id]
end LinearStudy
