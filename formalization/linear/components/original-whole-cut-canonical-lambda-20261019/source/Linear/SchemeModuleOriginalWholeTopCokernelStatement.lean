module
public import Linear.SchemeModuleOriginalWholeTopCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- Actual SAME-rank whole-cokernel class law as a geometric specialization boundary;this definition is not itself a proof. -/
def schemeModuleOriginalWholeTopCokernelStatement
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := HasDerivedCategory.standard X.Modules
  ∃ chi : schemeModuleInternalExt E N r ≅
      cokernel (schemeModuleHomPrecompose (N := N) (C.d r (r-1))),
    schemeModuleGlobalToInternalExtAll E N r
        (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha) ≫ chi.hom =
      (schemeModuleHomUnitAddEquiv (C.X r) N).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) (C.d r (r-1)))
/-- Every positive original rank satisfies the law,from actual source acyclicity and top bound. -/
theorem schemeModuleOriginalWholeTopCokernelStatement_proof
    (C : ChainComplex X.Modules ℕ) {E N : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hA : ∀ j q,IsZero (schemeModuleInternalExt (C.X j) N (q+1)))
    (hAbove : IsZero (C.X (r+1)))
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    schemeModuleOriginalWholeTopCokernelStatement C r alpha hAlpha a ha := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  refine ⟨schemeModuleOriginalWholeTopCokernelIso C N p alpha hAlpha
    (injectiveResolution N) hA hAbove,?_⟩
  exact schemeModuleOriginalSmallClass_wholeTopCokernel C p alpha hAlpha
    (injectiveResolution N) hA hAbove a ha
end LinearStudy
