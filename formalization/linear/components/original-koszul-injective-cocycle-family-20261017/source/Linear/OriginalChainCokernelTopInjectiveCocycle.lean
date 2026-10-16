module
public import Linear.OriginalChainTopInjectiveCocycle
public import Linear.ChainActualCokernelAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- Retain the SAME canonical original quotient augmentation. Its quasi-isomorphism
is DERIVED from source exactness;no comparison or class identity is supplied. -/
theorem originalChainCokernelTopInjectiveCocycle_exists
    (C : ChainComplex A ℕ) (he : ∀ p : ℕ,0 < p → C.ExactAt p)
    {N : A} (r : ℕ)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) (I : InjectiveResolution N) :
    letI := originalChainCokernelAugmentation_quasiIso C he
    ∃ (c : Cocycle ((CochainComplex.singleFunctor A 0).obj (cokernel (C.d 1 0))) I.cochainComplex (r : ℤ))
      (t : Cochain (originalChainAsCochain C) I.cochainComplex ((r : ℤ)-1)),
      CohomologyClass.mk (c.precomp (originalChainAugmentationAsCochain C (originalChainCokernelAugmentation C))) =
        CohomologyClass.mk ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι') ∧
      δ ((r : ℤ)-1) (r : ℤ) t =
        (c.precomp (originalChainAugmentationAsCochain C (originalChainCokernelAugmentation C))).val -
          ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι').val ∧
      originalChainTopExtClass C r (originalChainCokernelAugmentation C) a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) := by
  letI := originalChainCokernelAugmentation_quasiIso C he
  exact originalChainTopInjectiveCocycle_exists C r (originalChainCokernelAugmentation C) a ha I

end LinearStudy
