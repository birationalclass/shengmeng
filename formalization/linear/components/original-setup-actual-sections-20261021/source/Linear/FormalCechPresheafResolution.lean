/- Copyright (c) 2026 Joel Riou. Released under Apache 2.0. -/
module
public import Linear.FormalCechSimplicialResolution
public import Linear.AugmentedPointwiseWhiskering
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe w u v u' v'
namespace CategoryTheory.Limits.FormalCoproduct
/-- The ACTUAL native presheaf Cech augmentation is a quasi-isomorphism,
after applying any type-valued coefficient functor into an abelian category.
The target here is still the cover-generated terminal subpresheaf. -/
theorem shrinkYonedaCech_presheaf_augmentation_quasiIso
    {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [HasFiniteLimits C]
    (U : FormalCoproduct.{w} C)
    {A : Type u'} [Category.{v'} A] [Abelian A] (G : Type w ⥤ A) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj
        ((Functor.whiskeringRight Cᵒᵖ (Type w) A).obj G)).obj U.shrinkYonedaCech)) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro X
  let S := (((SimplicialObject.Augmented.whiskering _ _).obj
    ((Functor.whiskeringRight Cᵒᵖ (Type w) A).obj G)).obj U.shrinkYonedaCech)
  let E := (evaluation Cᵒᵖ A).obj X
  let T := ((SimplicialObject.Augmented.whiskering _ _).obj E).obj S
  have hT : QuasiIso (AlternatingFaceMapComplex.ε.app T) := by
    obtain ⟨ed⟩ := U.nonempty_extraDegeneracy_shrinkYonedaCech_evaluation X
    let e := LinearStudy.augmentedPointwiseWhiskeringIso U.shrinkYonedaCech G X
    have he : Arrow.mk (AlternatingFaceMapComplex.ε.app T) ≅
        Arrow.mk (AlternatingFaceMapComplex.ε.app
          (((SimplicialObject.Augmented.whiskering _ _).obj G).obj
            (((SimplicialObject.Augmented.whiskering _ _).obj
              ((evaluation Cᵒᵖ (Type w)).obj X)).obj U.shrinkYonedaCech))) := Arrow.isoMk
      ((SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex A).mapIso e)
      ((SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ A).mapIso e)
      (AlternatingFaceMapComplex.ε.naturality e.hom)
    exact ((HomologicalComplex.quasiIso A (.down ℕ)).arrow_mk_iso_iff he).mpr
      (ed.map G).homotopyEquiv.quasiIso_hom
  exact ((HomologicalComplex.quasiIso A (.down ℕ)).arrow_mk_iso_iff
    (LinearStudy.alternatingAugmentationWhiskeringArrowIso S E)).mpr hT
end CategoryTheory.Limits.FormalCoproduct
