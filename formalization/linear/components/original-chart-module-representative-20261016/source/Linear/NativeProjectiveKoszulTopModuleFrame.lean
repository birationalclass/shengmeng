module
public import Linear.TildeKoszulOriginalTopModuleFrame
public import Linear.NativeKoszulMappedChartBoundary
public import Linear.NativeKoszulFiniteTopTerm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] tildeKoszulOriginalTopModuleFrameLaw nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedTildeAffineIso CategoryTheory.Functor.mapHomologicalComplex

/-- Actual coefficient frame induced by the original native chart and
original top exterior-basis identification. -/
def nativeProjectiveKoszulTopChartModuleFrame [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  (Scheme.Modules.restrictFunctor j).obj
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ))) ≅
    (tilde.functor R).obj ((koszulComplex (Fintype.linearCombination R h)).X r) := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact tildeKoszulOriginalTopCoefficientIso R h (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha)
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k)

/-- Explicit normalization STATEMENT for the SAME actual native maps. -/
def nativeProjectiveKoszulTopChartModuleFrameLaw [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) : Prop :=
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  tildeKoszulOriginalTopModuleFrameLaw R h (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha)
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k)

/-- Prove actual MODULE identity in the CONSTRUCTED induced frame;
no independent frame,sign or desired module formula is assumed. -/
theorem nativeProjectiveKoszulTopChartModuleFrameLaw_proof [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    nativeProjectiveKoszulTopChartModuleFrameLaw 𝓑 b hb hgen H hH k a ha := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact tildeKoszulOriginalTopModuleFrameLaw_proof R h (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulComplex 𝓑 H hH k)
    (nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha)
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k)

end LinearStudy
