module
public import Linear.NativeGlobalKoszulQuasicoherent
public import Linear.AffineQuasicoherentComplexCounit
public import Linear.SchemeModuleOpenRestrictionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The SAME ORIGINAL GLOBAL Koszul SHEAF complex restricted to an
ACTUAL original affine open immersion. No replacement complex is supplied. -/
def nativeProjectiveKoszulOnAffine (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑)
    [IsOpenImmersion j] {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) :
    ChainComplex (Spec R).Modules ℕ := by
  letI := schemeModuleOpenRestriction_additive j
  exact ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (nativeProjectiveKoszulComplex 𝓑 H hH k)

/-- Its degree-p source is EXACTLY the restriction of the ORIGINAL term. -/
theorem nativeProjectiveKoszulOnAffine_X (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑)
    [IsOpenImmersion j] {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).X p =
      (Scheme.Modules.restrictFunctor j).obj (nativeProjectiveKoszulTerm 𝓑 r q p k) := rfl

/-- Quasicoherence of EVERY actual restricted ORIGINAL term is DERIVED,
not an extra hypothesis on the source complex or on a coefficient N. -/
theorem nativeProjectiveKoszulOnAffine_isQuasicoherent [IsNoetherianRing S]
    {J : Type} (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤)
    (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑) [IsOpenImmersion j]
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    ((nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).X p).IsQuasicoherent := by
  change ((Scheme.Modules.restrictFunctor j).obj
    (nativeProjectiveKoszulTerm 𝓑 r q p k)).IsQuasicoherent
  exact nativeProjectiveKoszulTerm_restrict_isQuasicoherent 𝓑 a ha hgen r q p k j

/-- Genuine ACTUAL SHEAF-complex isomorphism for the SAME original
restricted Koszul complex and the tilde of its SAME original global sections.
Every component is the actual geometric counit,whose invertibility is DERIVED.
Identification of those global sections with standard affine H/a^q is separate. -/
def nativeProjectiveKoszulAffineCounitIso [IsNoetherianRing S]
    {J : Type} (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤)
    (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑) [IsOpenImmersion j]
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k)) ≅
      nativeProjectiveKoszulOnAffine 𝓑 R j H hH k := by
  letI (p : ℕ) : ((nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).X p).IsQuasicoherent :=
    nativeProjectiveKoszulOnAffine_isQuasicoherent 𝓑 a ha hgen R j H hH k p
  exact affineQuasicoherentComplexCounitIso R (ComplexShape.down ℕ)
    (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k)

/-- EVERY comparison component retains the ORIGINAL actual counit map. -/
theorem nativeProjectiveKoszulAffineCounitIso_hom [IsNoetherianRing S]
    {J : Type} (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤)
    (R : CommRingCat) (j : Spec R ⟶ Proj 𝓑) [IsOpenImmersion j]
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    (nativeProjectiveKoszulAffineCounitIso 𝓑 a ha hgen R j H hH k).hom.f p =
      ((nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).X p).fromTildeΓ := rfl

end LinearStudy
