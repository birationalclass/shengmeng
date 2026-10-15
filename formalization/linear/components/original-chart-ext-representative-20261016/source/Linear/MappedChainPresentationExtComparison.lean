module
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Linear.MappedChainPresentationAugmentation
public import Linear.OriginalChainAugmentationSquareExt
public import Linear.OriginalChainMappedExtComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- The SAME actual target iso of one constructed presentation payload.
This is an object construction,not an assumed augmentation/Ext identity. -/
def mappedChainPresentationAugmentationTargetIso
    (p : mappedChainPresentationData F) (T : A) (ec : cokernel (p.1.d 1 0) ≅ T) :
    F.obj T ≅ p.2.2.2.1.pt :=
  mappedOriginalChainTargetCokernelChartIso F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 T ec

/-- DERIVE the actual original quotient-cofork augmentation's quasiiso
from the original augmentation and the independently PROVED whole square. -/
theorem mappedChainPresentationCoforkAugmentation_quasiIso
    (p : mappedChainPresentationData F) (T : A) (ec : cokernel (p.1.d 1 0) ≅ T)
    [QuasiIso (originalChainCokernelTargetAugmentation p.1 T ec)] :
    QuasiIso (originalChainCoforkAugmentation p.2.1 p.2.2.2.1) := by
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  letI := mappedOriginalChainAugmentation_quasiIso F p.1
    (originalChainCokernelTargetAugmentation p.1 T ec)
  exact originalChainAugmentationSquare_quasiIso _ p.2.1 p.2.2.1
    (mappedChainPresentationAugmentationTargetIso F p T ec)
    (mappedOriginalChainAugmentation F p.1 (originalChainCokernelTargetAugmentation p.1 T ec))
    (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
    (mappedOriginalChainCokernelTargetAugmentation_chart_comm F p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2 T ec)

variable [HasExt.{w} B] [HasDerivedCategory.{d} B]

/-- The constructed original cokernel/chart square induces the ACTUAL
Ext representative comparison. Retain the SAME target iso,quotient
augmentation and top functional. No square or Ext equality is an input. -/
theorem mappedChainPresentationTopExtClass_comparison
    (p : mappedChainPresentationData F) (T : A) (ec : cokernel (p.1.d 1 0) ≅ T)
    [QuasiIso (originalChainCokernelTargetAugmentation p.1 T ec)]
    (r : ℕ) (N : B) (b : p.2.1.X r ⟶ N) (hb : p.2.1.d (r+1) r ≫ b = 0) :
    letI := Functor.preservesFiniteLimits_of_preservesHomology F
    letI := Functor.preservesFiniteColimits_of_preservesHomology F
    letI := mappedOriginalChainAugmentation_quasiIso F p.1
      (originalChainCokernelTargetAugmentation p.1 T ec)
    letI := mappedChainPresentationCoforkAugmentation_quasiIso F p T ec
    (Ext.mk₀ (mappedChainPresentationAugmentationTargetIso F p T ec).hom).comp
      (originalChainTopExtClass p.2.1 r (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
        b hb) (zero_add _) =
      originalChainTopExtClass ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj p.1) r
        (mappedOriginalChainAugmentation F p.1 (originalChainCokernelTargetAugmentation p.1 T ec))
        (p.2.2.1.hom.f r ≫ b) (by
          change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj p.1).d (r+1) r) ≫
            p.2.2.1.hom.f r ≫ b = 0
          rw [← p.2.2.1.hom.comm_assoc]
          simp only [hb,comp_zero]) := by
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  letI := mappedOriginalChainAugmentation_quasiIso F p.1
    (originalChainCokernelTargetAugmentation p.1 T ec)
  exact originalChainTopExtClass_augmentationSquare _ p.2.1 p.2.2.1 r
    (mappedChainPresentationAugmentationTargetIso F p T ec)
    (mappedOriginalChainAugmentation F p.1 (originalChainCokernelTargetAugmentation p.1 T ec))
    (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
    (mappedOriginalChainCokernelTargetAugmentation_chart_comm F p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2 T ec) b hb

end LinearStudy
