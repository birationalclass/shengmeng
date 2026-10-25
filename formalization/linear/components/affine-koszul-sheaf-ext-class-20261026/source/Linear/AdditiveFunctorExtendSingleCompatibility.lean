module
public import Linear.AdditiveFunctorExtendNaturality
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

/-- At every original term,the constructed comparison commutes with the
native extension evaluation isomorphisms. -/
theorem additiveFunctorExtendXIso_comp_XIso (C : HomologicalComplex A c)
    {o : Option ι} {i : ι} (h : o = some i) :
    (additiveFunctorExtendXIso F C o).hom ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj C) h).hom =
      F.map (HomologicalComplex.extend.XIso C h).hom := by
  subst h
  simp [additiveFunctorExtendXIso,HomologicalComplex.extend.XIso]

/-- The ACTUAL extension/map comparison preserves the native single-term
identifications. This supplies the target comparison in the augmentation
square without an assumed equality of desired Ext classes. -/
theorem additiveFunctorExtendSingleIso_compatibility
    [DecidableEq ι] [DecidableEq ι'] (e : c.Embedding c') (E : A)
    (i : ι) (i' : ι') (h : e.f i = i') :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendSingleIso e E i i' h).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex F c' i').hom.app E =
      (additiveFunctorExtendComplexIso F ((HomologicalComplex.single A c i).obj E) e).hom ≫
        HomologicalComplex.extendMap
          ((HomologicalComplex.singleMapHomologicalComplex F c i).hom.app E) e ≫
        (HomologicalComplex.extendSingleIso e (F.obj E) i i' h).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.extendMap_f _ _ h,Functor.map_comp,Category.assoc]
  simp only [additiveFunctorExtendComplexIso,HomologicalComplex.extendXIso]
  erw [reassoc_of% (additiveFunctorExtendXIso_comp_XIso F
    ((HomologicalComplex.single A c i).obj E) (e.r_eq_some h))]
  simp only [Functor.comp_obj,Iso.inv_hom_id_assoc,← F.map_comp_assoc,
    Iso.inv_hom_id,Functor.map_id,Category.id_comp,Category.comp_id]

end LinearStudy