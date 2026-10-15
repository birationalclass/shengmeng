module
public import Linear.NativeGlobalKoszulAffineCounit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- The ACTUAL homology of the SAME original global Koszul restricts to
homology of its SAME actual restricted complex. This constructs just the
restriction comparison;no cut target or positive exactness is an input. -/
def nativeProjectiveKoszulActualRestrictionHomologyIso
    (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑) [IsOpenImmersion j]
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    (Scheme.Modules.restrictFunctor j).obj
      ((nativeProjectiveKoszulComplex 𝓑 H hH k).homology p) ≅
      (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).homology p := by
  exact (schemeModuleOpenRestriction_homologyIso j (ComplexShape.down ℕ)
    (nativeProjectiveKoszulComplex 𝓑 H hH k) p).symm

end LinearStudy