module
public import Linear.MappedChainPresentationOriginalExt
public import Linear.ChainCokernelAugmentationSourceEq
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
variable [HasExt.{wA} A] [HasDerivedCategory.{dA} A]
variable [HasExt.{wB} B] [HasDerivedCategory.{dB} B]

/-- Explicit STATEMENT for the SAME named original source,actual
presentation payload and PROVED source equality. Each augmentation and
top map is the actual original one,transported only through that equality.
The square/Ext equality is a conclusion,never a premise or data field. -/
def mappedChainPresentationNamedExtLaw
    (p : mappedChainPresentationData F) (C : ChainComplex A ℕ) (hC : p.1 = C)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) : Prop :=
  ∀ he : QuasiIso (originalChainCokernelTargetAugmentation C T e),
    letI := he
    letI := Functor.preservesFiniteLimits_of_preservesHomology F
    letI := Functor.preservesFiniteColimits_of_preservesHomology F
    ∀ {M : A} (r : ℕ) (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0),
      let ce := eqToIso (congrArg (fun K : ChainComplex A ℕ => cokernel (K.d 1 0)) hC) ≪≫ e
      letI := originalChainCokernelTargetAugmentation_quasiIso_sourceEq p.1 C hC T e he
      letI := mappedChainPresentationCoforkAugmentation_quasiIso F p T ce
      (originalChainTopExtClass C r (originalChainCokernelTargetAugmentation C T e) a ha).mapExactFunctor F =
        (Ext.mk₀ (mappedChainPresentationAugmentationTargetIso F p T ce).hom).comp
          (originalChainTopExtClass p.2.1 r (originalChainCoforkAugmentation p.2.1 p.2.2.2.1)
            (mappedChainPresentationOriginalTopFunctional F p r ((eqToIso hC).hom.f r ≫ a))
            (mappedChainPresentationOriginalTopFunctional_isCocycle F p r
              ((eqToIso hC).hom.f r ≫ a) (by cases hC;simpa using ha))) (zero_add _)

/-- PROVE the named-original statement by the constructed chart square,
native exact-functor action and source-equality invariance. -/
theorem mappedChainPresentationNamedExtLaw_proof
    (p : mappedChainPresentationData F) (C : ChainComplex A ℕ) (hC : p.1 = C)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) :
    mappedChainPresentationNamedExtLaw F p C hC T e := by
  intro he
  letI := he
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  intro M r a ha
  let ce := eqToIso (congrArg (fun K : ChainComplex A ℕ => cokernel (K.d 1 0)) hC) ≪≫ e
  letI := originalChainCokernelTargetAugmentation_quasiIso_sourceEq p.1 C hC T e he
  have z := mappedChainPresentationOriginalExt_mapExactFunctor F p T ce r
    ((eqToIso hC).hom.f r ≫ a) (by cases hC;simpa using ha)
  have hs := originalChainTopExtClass_cokernelSourceEq p.1 C hC T e r a ha
  rw [hs] at z
  exact z

end LinearStudy
