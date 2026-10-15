module
public import Linear.MappedChainCokernelAugmentationLaw
public import Linear.MappedChainPresentationData
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

/-- Explicit STATEMENT of the actual augmentation square for ONE actual
presentation-data payload,universally quantified over final target T and
the actual original cokernel identification ec. No desired square is a
field in the payload,and this definition alone is not a proof. -/
def mappedChainPresentationAugmentationLaw
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (d : mappedChainPresentationData F) : Prop :=
  ∀ (T : A) (ec : cokernel (d.1.d 1 0) ≅ T),
    mappedOriginalChainCokernelAugmentationChartLaw F d.1 d.2.1 d.2.2.1
      d.2.2.2.1 d.2.2.2.2 T ec

/-- PROVE the whole actual augmentation square from the SAME constructed
complexes,source iso and original quotient cofork/colimit. Keep the final
target AFTER the payload so concrete geometry is elaborated only once. -/
theorem mappedChainPresentationAugmentationLaw_proof
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (d : mappedChainPresentationData F) : mappedChainPresentationAugmentationLaw F d := by
  intro T ec
  exact mappedOriginalChainCokernelAugmentationChartLaw_proof F d.1 d.2.1 d.2.2.1
    d.2.2.2.1 d.2.2.2.2 T ec

end LinearStudy
