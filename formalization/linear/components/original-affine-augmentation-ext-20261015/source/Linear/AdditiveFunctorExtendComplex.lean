module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
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

/-- Native termwise comparison: an additive functor sends the extension's
zero terms to zero and preserves each SAME original nonzero-index term. -/
def additiveFunctorExtendXIso (C : HomologicalComplex A c) :
    ∀ i : Option ι,F.obj (HomologicalComplex.extend.X C i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj C) i
  | some _ => Iso.refl _
  | none => F.mapZeroObject

/-- The comparison respects the ACTUAL extended differential,including
all zero terms outside the embedding image. -/
theorem additiveFunctorExtendXIso_comm (C : HomologicalComplex A c) (i j : Option ι) :
    (additiveFunctorExtendXIso F C i).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj C) i j =
      F.map (HomologicalComplex.extend.d C i j) ≫ (additiveFunctorExtendXIso F C j).hom := by
  cases i <;> cases j <;>
    simp [additiveFunctorExtendXIso,HomologicalComplex.extend.d,HomologicalComplex.extend.X,Functor.map_zero,zero_comp,comp_zero]

/-- Construct the ACTUAL whole-complex comparison between mapping an
extended complex and extending its mapped original complex. No arbitrary
comparison is an input;its components retain the original terms. -/
def additiveFunctorExtendComplexIso (C : HomologicalComplex A c) (e : c.Embedding c') :
    ((F.mapHomologicalComplex c').obj (C.extend e)) ≅
      (((F.mapHomologicalComplex c).obj C).extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => additiveFunctorExtendXIso F C (e.r i))
    (fun i j _ => additiveFunctorExtendXIso_comm F C (e.r i) (e.r j))

end LinearStudy