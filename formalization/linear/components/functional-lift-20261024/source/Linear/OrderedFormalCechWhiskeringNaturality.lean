module
public import Linear.OrderedFormalCechCoefficientFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v w v' w'
variable {X : Scheme.{u}} {A : Type w} [Category.{v} A] [Preadditive A]
  {B : Type w'} [Category.{v'} B] [Preadditive B]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
/-- The SAME original ordered-complex/additive-forgetting comparison is
natural in ORIGINAL coefficient-presheaf transformations,including signs. -/
theorem orderedFormalCechWhiskeringIso_coefficient_naturality
    {F G : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤ A} (a : F ⟶ G)
    (H : A ⥤ B) [H.Additive] :
    (H.mapHomologicalComplex (.up ℕ)).map ((orderedFormalCechCoefficientFunctor U).map a) ≫
        (orderedFormalCechWhiskeringIso U G H).hom =
      (orderedFormalCechWhiskeringIso U F H).hom ≫
        (orderedFormalCechCoefficientFunctor U).map (Functor.whiskerRight a H) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change H.map (a.app (op (AlgebraicGeometry.Scheme.Modules.orderedCechFormalObject U n))) ≫ 𝟙 _ =
    𝟙 _ ≫ H.map (a.app (op (AlgebraicGeometry.Scheme.Modules.orderedCechFormalObject U n)))
  simp only [Category.comp_id,Category.id_comp]
end LinearStudy
