module
public import Linear.NativeHomogeneousGlobalSection
public import Linear.NativeIntegerTwistSectionFrames
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The actual positive homogeneous section of the original graded ring.
Its value at every original homogeneous prime is ell/1. -/
def nativePositiveHomogeneousGlobalSection (m : ℕ) (ell : 𝓑 m) :
    Γ(nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ), ⊤) :=
  nativeProjectiveModuleHomogeneousGlobalSection 𝓑
    (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑)
    (m : ℤ) ⟨ell,by
      simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,if_true,
        Int.toNat_natCast] using ell.property⟩

/-- On any actual open inside the coordinate chart, the chart expression
ell/a^m becomes the actual global polynomial section after multiplication
by the original coordinate frame a^m. -/
theorem nativePositiveHomogeneousGlobalSection_frame (m : ℕ) (ell : 𝓑 m)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) :
    nativeIntegerTwistSectionFrame 𝓑 a ha (m : ℤ) (op U) (fun p => hU p.2)
      (((Proj 𝓑).presheaf.map (homOfLE hU).op).hom
        ((Proj.basicOpenIsoAway 𝓑 a ha one_pos).hom.hom
          (HomogeneousLocalization.Away.mk 𝓑 ha m (ell : S)
            (by simpa using ell.property)))) =
      (nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).map
        (homOfLE (show U ≤ ⊤ from le_top)).op
          (nativePositiveHomogeneousGlobalSection 𝓑 m ell) := by
  apply Subtype.ext
  funext p
  change nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hU p.2) (m : ℤ)
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
        (HomogeneousLocalization.mapId 𝓑 (Submonoid.powers_le.mpr (hU p.2))
          (HomogeneousLocalization.Away.mk 𝓑 ha m (ell : S)
            (by simpa using ell.property)))) = LocalizedModule.mk (ell : S) 1
  rw [nativePrimeIntegerTwistEquiv_ofNat]
  simp only [HomogeneousLocalization.Away.mk,HomogeneousLocalization.mapId,
    HomogeneousLocalization.map_mk]
  rw [nativeHomogeneousLocalRingModuleEmbedding_mk,nativeProjectivePrimeTwistEquiv_mk]
  exact LocalizedModule.mk_cancel
    (⟨a^m,p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU p.2) m⟩ :
      p.1.asHomogeneousIdeal.toIdeal.primeCompl) (ell : S)

/-- Positive homogeneous sections respect addition in the actual original
module localizations, for later finite monomial assembly. -/
theorem nativePositiveHomogeneousGlobalSection_add (m : ℕ) (ell t : 𝓑 m) :
    nativePositiveHomogeneousGlobalSection 𝓑 m (ell+t) =
      nativePositiveHomogeneousGlobalSection 𝓑 m ell +
        nativePositiveHomogeneousGlobalSection 𝓑 m t := by
  apply Subtype.ext
  funext p
  change LocalizedModule.mk ((ell : S)+(t : S)) 1 =
    LocalizedModule.mk (ell : S) 1 + LocalizedModule.mk (t : S) 1
  simpa only [one_smul,one_mul] using (LocalizedModule.mk_add_mk
    (m1 := (ell : S)) (m2 := (t : S)) (s1 := (1 : p.1.asHomogeneousIdeal.toIdeal.primeCompl))
    (s2 := (1 : p.1.asHomogeneousIdeal.toIdeal.primeCompl))).symm
end LinearStudy
