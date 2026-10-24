module
public import Linear.SchemeModuleOpenKoszulDataSourceEq
public import Linear.NativeKoszulMappedChartComplexIdentity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  tildeFunctionKoszulComplex schemeModuleOpenKoszulChartData
  nativeProjectiveKoszulMappedPresentationData
  schemeModuleOpenKoszulChartData_of_sourceIdentification
/-- ACTUAL original away chart,retaining its literal ring,inclusion and
equations. Only the source of the precompiled actual chain iso is
transported; no dependent package cast and no desired Ext law is input. -/
def nativeProjectiveOpenKoszulExactChart [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ B 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ B q) (k : ℤ)
    (z : S) (hz : z ∈ B 1) :=
  schemeModuleOpenKoszulChartData_of_sourceIdentification
    (CommRingCat.of (HomogeneousLocalization.Away B z))
    (Proj.awayι B z hz one_pos)
    (fun i => HomogeneousLocalization.Away.mk B hz q (H i) (by simpa using hH i))
    (nativeProjectiveKoszulComplex B H hH k)
    (nativeProjectiveKoszulMappedPresentationData B b hb hgen H hH k z hz)
    (nativeProjectiveKoszulMappedPresentationData_source B b hb hgen H hH k z hz)
    (nativeKoszulMappedChartComplex_identity B b hb hgen H hH k z hz)
end LinearStudy

