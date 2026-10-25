module
public import Linear.AdditiveFunctorExtendComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u' w w'
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
variable {B : Type u'} [Category.{v'} B] [Preadditive B] [HasZeroObject B]
variable (F : A ⥤ B) [F.Additive]
variable {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The actual term comparison retains EVERY original chain-map component,
including the zero objects inserted by native extension. -/
theorem additiveFunctorExtendXIso_naturality
    {C D : HomologicalComplex A c} (phi : C ⟶ D) (i : Option ι) :
    F.map (HomologicalComplex.extend.mapX phi i) ≫ (additiveFunctorExtendXIso F D i).hom =
      (additiveFunctorExtendXIso F C i).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map phi) i := by
  cases i <;> simp [additiveFunctorExtendXIso,HomologicalComplex.extend.mapX,
    HomologicalComplex.extend.X,Functor.map_zero,comp_zero,zero_comp]

/-- The constructed whole-complex comparison is natural in the ACTUAL
original chain map. This is needed for the actual augmentation square. -/
theorem additiveFunctorExtendComplexIso_naturality
    {C D : HomologicalComplex A c} (phi : C ⟶ D) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap phi e) ≫
        (additiveFunctorExtendComplexIso F D e).hom =
      (additiveFunctorExtendComplexIso F C e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map phi) e := by
  ext i
  exact additiveFunctorExtendXIso_naturality F phi (e.r i)

end LinearStudy