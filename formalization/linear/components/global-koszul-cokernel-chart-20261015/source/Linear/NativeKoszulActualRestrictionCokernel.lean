module
public import Linear.NativeGlobalKoszulAffineCounit
public import Linear.SchemeModuleRestrictionCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- Restrict the ACTUAL cokernel of the SAME original global d1 to the
ACTUAL cokernel of its restricted differential. This uses native cokernel
preservation directly;no desired geometric target is assumed. -/
def nativeProjectiveKoszulActualRestrictionCokernelIso
    (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑) [IsOpenImmersion j]
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) :
    (Scheme.Modules.restrictFunctor j).obj
      (cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0)) ≅
      cokernel ((nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).d 1 0) := by
  exact schemeModuleOpenRestrictionCokernelIso j
    ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0)

end LinearStudy