module
public import Linear.ChainStandardTopExtExactFunctorProof
public import Linear.SchemeModuleOpenRestrictionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- ACTUAL module-sheaf open restriction of the SAME resolution class is
the roof of its ACTUAL restricted cochain complex and augmentation.
Exactness/additivity of original restriction and standard Ext/derived
categories are DERIVED,not added original premises. No internal SHEAF Ext
or affine-module representative comparison is claimed here. -/
def schemeModuleOriginalChainTopExtOpenRestrictionProof
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (C : ChainComplex Y.Modules ℕ) {E M : Y.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ Y.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :=
  letI := schemeModuleOpenRestriction_preservesFiniteLimits j
  letI := schemeModuleOpenRestriction_additive j
  originalChainExplicitStandardTopExtClassMapProof (Scheme.Modules.restrictFunctor j)
    C r alpha hAlpha a ha

end LinearStudy
