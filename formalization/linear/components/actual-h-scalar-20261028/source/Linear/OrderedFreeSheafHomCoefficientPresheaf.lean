module
public import Linear.OrderedFreeSheafHomCoefficientFactors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
attribute [local irreducible] orderedFreeSheafHomCoefficientPresheafIso
/-- The SAME presheaf factor commutes with original coefficient morphisms,
including actual section maps on ALL ordered intersection terms. -/
theorem orderedFreeSheafHomCoefficientPresheafIso_coefficient_naturality
    (X : Scheme.{u}) {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (a : F ⟶ G) :
    Functor.whiskerLeft ((orderedFreeOpenFormalPresheafFunctor X) ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).op
        (preadditiveYoneda.map a) ≫ (orderedFreeSheafHomCoefficientPresheafIso X G).hom =
      (orderedFreeSheafHomCoefficientPresheafIso X F).hom ≫
        (FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}).map a.hom := by
  let P := orderedFreeOpenFormalPresheafFunctor X
  let K := topOpenFreeAbelianPresheafFunctor X
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let E := FormalCoproduct.evalOp.{u} X.Opens AddCommGrpCat.{u}
  apply NatTrans.ext
  funext V
  have h₁ := congrArg (fun t => t.app (op (P.obj V.unop)))
    (nativeAdjunctionHomPresheafIso_coefficient_naturality adj a)
  have h₂ := congrArg (fun t => t.app V)
    (formalCoproductContravariantEvaluationIso_coefficient_naturality K
      (preadditiveYoneda.obj F.obj) (preadditiveYoneda.obj G.obj) (preadditiveYoneda.map a.hom))
  have h₃ := congrArg (fun t => (E.map t).app V)
    (topOpenFreeAbelianPresheafHomPresheafIso_coefficient_naturality X a)
  simp only [Functor.map_comp,NatTrans.comp_app] at h₃
  have s₁ : CommSq ((preadditiveYoneda.map a).app (op ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (P.obj V.unop))))
      ((nativeAdjunctionHomPresheafIso adj F).hom.app (op (P.obj V.unop)))
      ((nativeAdjunctionHomPresheafIso adj G).hom.app (op (P.obj V.unop)))
      ((preadditiveYoneda.map a.hom).app (op (P.obj V.unop))) := ⟨h₁⟩
  have s₂ : CommSq ((preadditiveYoneda.map a.hom).app (op (P.obj V.unop)))
      ((formalCoproductContravariantEvaluationIso K (preadditiveYoneda.obj F.obj)).hom.app V)
      ((formalCoproductContravariantEvaluationIso K (preadditiveYoneda.obj G.obj)).hom.app V)
      ((E.map (Functor.whiskerLeft K.op (preadditiveYoneda.map a.hom))).app V) := ⟨h₂⟩
  have s₃ : CommSq ((E.map (Functor.whiskerLeft K.op (preadditiveYoneda.map a.hom))).app V)
      ((E.mapIso (topOpenFreeAbelianPresheafHomPresheafIso X F)).hom.app V)
      ((E.mapIso (topOpenFreeAbelianPresheafHomPresheafIso X G)).hom.app V)
      ((E.map a.hom).app V) := ⟨h₃⟩
  simp only [NatTrans.comp_app,Functor.whiskerLeft_app,
    orderedFreeSheafHomCoefficientPresheafIso_hom_app]
  exact (s₁.vert_comp (s₂.vert_comp s₃)).w
end LinearStudy
