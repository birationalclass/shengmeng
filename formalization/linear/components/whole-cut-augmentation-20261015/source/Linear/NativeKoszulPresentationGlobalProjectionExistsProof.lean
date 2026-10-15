module
public import Linear.NativeKoszulPresentationDataObjects
public import Linear.NativeKoszulSupportedCokernelUnit
public import Linear.SchemeModulePresentationProjectionExists
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedPresentationData CategoryTheory.Functor.mapHomologicalComplex

/-- ACTUAL proof term:the constructed supported GLOBAL comparison sends
its ORIGINAL quotient projection to the native adjoint of the SAME
ORIGINAL chart quotient projection. Original source and target are
identified by proved object equalities. Derive the native unit condition
from ORIGINAL ambient coverage;the desired equality is never a premise.
All integer twists and original ideals/nilpotents retained. The inferred
proposition requires independent exact-type and foundational-dependency review before counting. -/
def nativeProjectiveKoszulPresentationGlobalProjectionExistsProof [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    (hc : ∀ x : Proj 𝓑,x ∈ Proj.basicOpen 𝓑 a ∨
      ∃ i : Fin r,x ∈ Proj.basicOpen 𝓑 (H i)) :=
  let j := Proj.awayι 𝓑 a ha one_pos
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  let d := nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha
  let hu := schemeModuleCokernelRestrictionUnit_isIso_of_complex_eq j d.1
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedPresentationData_source 𝓑 b hb hgen H hH k a ha)
    (nativeProjectiveKoszul_cokernelRestrictionUnit_isIso 𝓑 b hb hgen H hH k a ha hc)
  schemeModuleMappedPresentationDataGlobalProjection_exists j d hu

end LinearStudy
