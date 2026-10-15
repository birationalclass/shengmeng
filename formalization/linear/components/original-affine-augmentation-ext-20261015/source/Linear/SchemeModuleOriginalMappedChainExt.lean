module
public import Linear.ChainStandardMappedExtLaw
public import Linear.SchemeModuleOpenRestrictionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- Actual open restriction of the original class equals the class of the
SAME restricted CHAIN complex,augmentation and top functional. All
categorical prerequisites are derived. This Prop is a statement. -/
def schemeModuleOriginalMappedChainExtLaw
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ChainComplex Y.Modules ℕ) {E M : Y.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ Y.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) : Prop :=
  letI := schemeModuleOpenRestriction_preservesFiniteLimits j
  letI := schemeModuleOpenRestriction_additive j
  originalChainStandardMappedExtLaw (Scheme.Modules.restrictFunctor j)
    C r alpha hAlpha a ha

/-- The actual native restriction identity is PROVED,not assumed. -/
theorem schemeModuleOriginalMappedChainExtLaw_proof
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ChainComplex Y.Modules ℕ) {E M : Y.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ Y.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    schemeModuleOriginalMappedChainExtLaw j C r alpha hAlpha a ha := by
  letI := schemeModuleOpenRestriction_preservesFiniteLimits j
  letI := schemeModuleOpenRestriction_additive j
  exact originalChainStandardMappedExtLaw_proof (Scheme.Modules.restrictFunctor j)
    C r alpha hAlpha a ha

end LinearStudy
