module
public import Linear.TildeKoszulMappedOriginalModuleExt
public import Linear.NativeKoszulMappedChartBoundary
public import Linear.TildeKoszulOriginalCutCofork
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] tildeKoszulMappedOriginalModuleExtLaw
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedTildeAffineIso CategoryTheory.Functor.mapHomologicalComplex

/-- Smaller native graded-chart boundary for the SAME actual Koszul
class/MODULE representative. The actual chart iso is already constructed.
Keep native objects abstract before original-geometry specialization. -/
def nativeProjectiveKoszulChartModuleExtLaw [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (T : (Proj 𝓑).Modules)
    (e : cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0) ≅ T) : Prop :=
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  tildeKoszulMappedOriginalModuleExtLaw R h (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha) T e

theorem nativeProjectiveKoszulChartModuleExtLaw_proof [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (T : (Proj 𝓑).Modules)
    (e : cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0) ≅ T) :
    nativeProjectiveKoszulChartModuleExtLaw 𝓑 b hb hgen H hH k a ha T e := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact tildeKoszulMappedOriginalModuleExtLaw_proof R h (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha) T e

end LinearStudy
