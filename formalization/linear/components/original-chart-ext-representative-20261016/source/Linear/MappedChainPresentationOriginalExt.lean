module
public import Linear.MappedChainPresentationExtComparison
public import Linear.ChainTopExtExactFunctorMappedChain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' wA dA wB dB
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- The actual top functional on the SAME chart complex is transported
from the original functional through the constructed whole-chain iso. -/
def mappedChainPresentationOriginalTopFunctional
    (p : mappedChainPresentationData F) {M : A} (r : ℕ) (a : p.1.X r ⟶ M) :
    p.2.1.X r ⟶ F.obj M := p.2.2.1.inv.f r ≫ F.map a

/-- Its cocycle condition follows from the ACTUAL differential square
and original cocycle. It is not an additional geometric hypothesis. -/
theorem mappedChainPresentationOriginalTopFunctional_isCocycle
    (p : mappedChainPresentationData F) {M : A} (r : ℕ) (a : p.1.X r ⟶ M)
    (ha : p.1.d (r+1) r ≫ a = 0) :
    p.2.1.d (r+1) r ≫ mappedChainPresentationOriginalTopFunctional F p r a = 0 := by
  dsimp only [mappedChainPresentationOriginalTopFunctional]
  rw [← p.2.2.1.inv.comm_assoc]
  change p.2.2.1.inv.f (r+1) ≫ F.map (p.1.d (r+1) r) ≫ F.map a = 0
  rw [← F.map_comp,ha,F.map_zero,comp_zero]

variable [HasExt.{wB} B] [HasDerivedCategory.{dB} B]

/-- Identify the actual chart quotient-roof with the SAME mapped original
roof,including the constructed target iso and transported original top
functional. No augmentation square or Ext-class identity is assumed. -/
theorem mappedChainPresentationOriginalTopExt_comparison
    (p : mappedChainPresentationData F) (T : A) (ec : cokernel (p.1.d 1 0) ≅ T)
    [QuasiIso (originalChainCokernelTargetAugmentation p.1 T ec)]
    {M : A} (r : ℕ) (a : p.1.X r ⟶ M) (ha : p.1.d (r+1) r ≫ a = 0) :
    letI := Functor.preservesFiniteLimits_of_preservesHomology F
    letI := Functor.preservesFiniteColimits_of_preservesHomology F
    letI := mappedOriginalChainAugmentation_quasiIso F p.1
      (originalChainCokernelTargetAugmentation p.1 T ec)
    letI := mappedChainPresentationCoforkAugmentation_quasiIso F p T ec
    (Ext.mk₀ (mappedChainPresentationAugmentationTargetIso F p T ec).hom).comp
      (originalChainTopExtClass p.2.1 r (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
        (mappedChainPresentationOriginalTopFunctional F p r a)
        (mappedChainPresentationOriginalTopFunctional_isCocycle F p r a ha)) (zero_add _) =
      originalChainTopExtClass ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj p.1) r
        (mappedOriginalChainAugmentation F p.1 (originalChainCokernelTargetAugmentation p.1 T ec))
        (F.map a) (by change F.map (p.1.d _ _) ≫ F.map a = 0;rw [← F.map_comp,ha,F.map_zero]) := by
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  letI := mappedOriginalChainAugmentation_quasiIso F p.1
    (originalChainCokernelTargetAugmentation p.1 T ec)
  have h := mappedChainPresentationTopExtClass_comparison F p T ec r (F.obj M)
    (mappedChainPresentationOriginalTopFunctional F p r a)
    (mappedChainPresentationOriginalTopFunctional_isCocycle F p r a ha)
  have hi := congrArg (fun z => z.f r) p.2.2.1.hom_inv_id
  simp only [HomologicalComplex.comp_f,HomologicalComplex.id_f] at hi
  have hf : p.2.2.1.hom.f r ≫ mappedChainPresentationOriginalTopFunctional F p r a = F.map a := by
    dsimp only [mappedChainPresentationOriginalTopFunctional]
    rw [← Category.assoc,hi,Category.id_comp]
  simpa only [hf] using h

variable [HasExt.{wA} A] [HasDerivedCategory.{dA} A]

/-- Native exact-functor action on the SAME original Ext class equals the
actual chart quotient-roof,with its constructed target iso and original
functional. Both the square and the derived-class identification are proved. -/
theorem mappedChainPresentationOriginalExt_mapExactFunctor
    (p : mappedChainPresentationData F) (T : A) (ec : cokernel (p.1.d 1 0) ≅ T)
    [QuasiIso (originalChainCokernelTargetAugmentation p.1 T ec)]
    {M : A} (r : ℕ) (a : p.1.X r ⟶ M) (ha : p.1.d (r+1) r ≫ a = 0) :
    letI := Functor.preservesFiniteLimits_of_preservesHomology F
    letI := Functor.preservesFiniteColimits_of_preservesHomology F
    letI := mappedChainPresentationCoforkAugmentation_quasiIso F p T ec
    (originalChainTopExtClass p.1 r (originalChainCokernelTargetAugmentation p.1 T ec) a ha).mapExactFunctor F =
      (Ext.mk₀ (mappedChainPresentationAugmentationTargetIso F p T ec).hom).comp
        (originalChainTopExtClass p.2.1 r (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
          (mappedChainPresentationOriginalTopFunctional F p r a)
          (mappedChainPresentationOriginalTopFunctional_isCocycle F p r a ha)) (zero_add _) := by
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  rw [originalChainTopExtClass_mapExactFunctor_eq_mappedChain]
  exact (mappedChainPresentationOriginalTopExt_comparison F p T ec r a ha).symm

end LinearStudy
