module
public import Linear.OriginalChainStandardTopInjectiveCocycle
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Statement of SAME original all-degree representative and actual homotopy,
quantified over EVERY coefficient injective resolution. This is a proposition
definition;the next theorem proves it. -/
def originalChainExplicitStandardTopInjectiveStatement
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := HasExt.standard A
  letI := HasDerivedCategory.standard A
  letI := hAlpha
  ∀ I : InjectiveResolution N,
    ∃ (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) I.cochainComplex (r : ℤ))
      (t : Cochain (originalChainAsCochain C) I.cochainComplex ((r : ℤ)-1)),
      CohomologyClass.mk (c.precomp (originalChainAugmentationAsCochain C alpha)) =
        CohomologyClass.mk ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι') ∧
      δ ((r : ℤ)-1) (r : ℤ) t =
        (c.precomp (originalChainAugmentationAsCochain C alpha)).val -
          ((originalChainOrderedTopCocycle C r a ha).postcomp I.ι').val ∧
      originalChainTopExtClass C r alpha a ha =
        I.extEquivCohomologyClass.symm (CohomologyClass.mk c)

/-- Actual proof of the statement for ALL injective resolutions. -/
theorem originalChainExplicitStandardTopInjectiveStatement_proof
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    originalChainExplicitStandardTopInjectiveStatement C r alpha hAlpha a ha := by
  intro I
  exact originalChainExplicitStandardTopInjectiveCocycleProof C r alpha hAlpha a ha I

end LinearStudy
