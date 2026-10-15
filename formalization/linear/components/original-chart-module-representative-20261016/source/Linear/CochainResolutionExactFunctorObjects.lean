module
public import Linear.CochainResolutionExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' w w'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Map the ACTUAL augmentation by an exact functor and its native
single-complex comparison. This retains the original source/map. -/
def mappedCochainResolutionAugmentation (K : CochainComplex A ℤ) {E : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (CochainComplex.singleFunctor B 0).obj (F.obj E) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).map alpha ≫
    (F.mapCochainComplexSingleFunctor 0).hom.app E

/-- Exactness of the functor DERIVES the mapped augmentation quasiiso;
this is not a new desired comparison or a local projectivity premise. -/
theorem mappedCochainResolutionAugmentation_quasiIso
    (K : CochainComplex A ℤ) {E : A}
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha] :
    QuasiIso (mappedCochainResolutionAugmentation F K alpha) := by
  dsimp [mappedCochainResolutionAugmentation]
  infer_instance

/-- Map the original shifted cocycle and the native single comparison,
preserving its degree. No replacement functional is supplied. -/
def mappedCochainResolutionCocycle (K : CochainComplex A ℤ) {M : A} (r : ℕ)
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    ShiftedHom ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((CochainComplex.singleFunctor B 0).obj (F.obj M)) (r:ℤ) :=
  (ShiftedHom.map beta (F.mapHomologicalComplex (ComplexShape.up ℤ))).comp
    (.mk₀ 0 rfl ((F.mapCochainComplexSingleFunctor 0).hom.app M)) (zero_add _)

/-- Actual roof built from the actual mapped complex and augmentation.
Equality with Ext.mapExactFunctor of the original roof remains to prove. -/
def mappedCochainResolutionExtClass [HasExt.{w} B] [HasDerivedCategory.{w'} B]
    (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    Ext.{w} (F.obj E) (F.obj M) r := by
  letI := mappedCochainResolutionAugmentation_quasiIso F K alpha
  exact cochainResolutionExtClass ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) r
    (mappedCochainResolutionAugmentation F K alpha) (mappedCochainResolutionCocycle F K r beta)

end LinearStudy
