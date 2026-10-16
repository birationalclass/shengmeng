module
public import Linear.OriginalChainOrderedTopCocycle
public import Linear.CochainResolutionInjectiveCocycle
public import Linear.CochainClassEqBoundary
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

/-- For EVERY original degree and ANY injective resolution,construct an actual
representative of the SAME ordered roof and its ACTUAL source cochain homotopy.
The local restriction and iterated-source identifications remain separate. -/
theorem originalChainTopInjectiveCocycle_exists
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) (I : InjectiveResolution N) :
    ∃ (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ))
      (t : Cochain (originalChainAsCochain C) I.cochainComplex ((r : ℤ)-1)),
      CohomologyClass.mk (c.precomp (originalChainAugmentationAsCochain C alpha)) =
        CohomologyClass.mk ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι') ∧
      δ ((r : ℤ)-1) (r : ℤ) t =
        (c.precomp (originalChainAugmentationAsCochain C alpha)).val -
          ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι').val ∧
      originalChainTopExtClass C r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c) := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  obtain ⟨c,hc,hclass⟩ := cochainResolutionInjectiveCocycle_exists
    (originalChainAsCochain C) r (originalChainAugmentationAsCochain C alpha)
    (originalChainOrderedTopCocycle C r a ha) I
  obtain ⟨t,ht⟩ := cochainClassEq_boundary_exists (r : ℤ) _ _ hc
  refine ⟨c,t,hc,ht,?_⟩
  rw [originalChainTopExtClass_orderedCocycle]
  exact hclass

end LinearStudy
