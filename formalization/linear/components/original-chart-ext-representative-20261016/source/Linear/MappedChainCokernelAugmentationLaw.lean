module
public import Linear.MappedChainCokernelAugmentationSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- An explicit named STATEMENT of the actual original augmentation
square. This definition is not a proof or an assumed comparison. -/
def mappedOriginalChainCokernelAugmentationChartLaw
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q)
    (T : A) (ec : cokernel (C.d 1 0) ≅ T) : Prop :=
  mappedOriginalChainAugmentation F C (originalChainCokernelTargetAugmentation C T ec) ≫
      (ChainComplex.single₀ B).map (mappedOriginalChainTargetCokernelChartIso F C D gamma Q hQ T ec).hom =
    gamma.hom ≫ originalChainCoforkAugmentation D Q

/-- The named actual augmentation square is PROVED from the same actual
cofork universal property and constructed target comparison. -/
theorem mappedOriginalChainCokernelAugmentationChartLaw_proof
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (gamma : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q)
    (T : A) (ec : cokernel (C.d 1 0) ≅ T) :
    mappedOriginalChainCokernelAugmentationChartLaw F C D gamma Q hQ T ec :=
  mappedOriginalChainCokernelTargetAugmentation_chart_comm F C D gamma Q hQ T ec

end LinearStudy
