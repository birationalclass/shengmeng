module
public import Linear.SchemeModuleOriginalExtOpenRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- This names the ACTUAL equality between native exact-functor action
and the actual mapped-complex roof. It is a STATEMENT,not a proof.
All categorical prerequisites are constructed from the open immersion. -/
def schemeModuleOriginalChainTopExtOpenRestrictionLaw
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ChainComplex Y.Modules ℕ) {E M : Y.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ Y.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := schemeModuleOpenRestriction_preservesFiniteLimits j
  letI := schemeModuleOpenRestriction_additive j
  letI := HasExt.standard Y.Modules
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasExt.standard X.Modules
  letI := HasDerivedCategory.standard X.Modules
  letI := hAlpha
  (originalChainTopExtClass C r alpha a ha).mapExactFunctor (Scheme.Modules.restrictFunctor j) =
    originalChainMappedTopExtClass (Scheme.Modules.restrictFunctor j) C r alpha a ha

/-- Prove the named law using the actual exact-functor/roof comparison.
The desired equality is not an input; no affine Ext equivalence is assumed. -/
theorem schemeModuleOriginalChainTopExtOpenRestrictionLaw_proof
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ChainComplex Y.Modules ℕ) {E M : Y.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ Y.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    schemeModuleOriginalChainTopExtOpenRestrictionLaw j C r alpha hAlpha a ha := by
  exact schemeModuleOriginalChainTopExtOpenRestrictionProof j C r alpha hAlpha a ha

end LinearStudy