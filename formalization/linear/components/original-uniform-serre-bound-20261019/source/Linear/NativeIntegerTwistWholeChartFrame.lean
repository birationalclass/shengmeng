module
public import Linear.NativeIntegerTwistSectionFrames
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- If the ORIGINAL degree-one coordinate is nowhere zero,the actual
integer-power section frame glues on the WHOLE original Proj presheaf.
Every component and restriction map is the SAME original fraction map. -/
def nativeIntegerTwistWholePresheafIso (a : S) (ha : a ∈ 𝓑 1)
    (hp : ∀ p : ProjectiveSpectrum 𝓑,a ∉ p.asHomogeneousIdeal) (k : ℤ) :
    PresheafOfModules.unit (Proj 𝓑).ringCatSheaf.obj ≅
      nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k :=
  PresheafOfModules.isoMk (fun U => by
    letI := nativeProjectiveModuleSectionGroup 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k U
    letI := nativeProjectiveModuleSectionModule 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k U
    exact (nativeIntegerTwistSectionFrame 𝓑 a ha k U (fun p => hp p.1)).toModuleIso)
    (by intros; apply ModuleCat.hom_ext; rfl)

/-- Genuine WHOLE-Proj native structure-module to integer-twist SHEAF
isomorphism,constructed from the original coordinate-power frames. -/
def nativeIntegerTwistWholeSheafIso (a : S) (ha : a ∈ 𝓑 1)
    (hp : ∀ p : ProjectiveSpectrum 𝓑,a ∉ p.asHomogeneousIdeal) (k : ℤ) :
    SheafOfModules.unit (Proj 𝓑).ringCatSheaf ≅
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (nativeIntegerTwistWholePresheafIso 𝓑 a ha hp k)

/-- Native whole-chart coverage DERIVES coordinate nonvanishing at ALL
original Proj primes,before applying the SAME integer-power sheaf frame.
The coverage hypothesis is explicit here and derived in original applications. -/
def nativeIntegerTwistWholeSheafIsoOfBasicOpenTop (a : S) (ha : a ∈ 𝓑 1)
    (htop : Proj.basicOpen 𝓑 a = ⊤) (k : ℤ) :
    SheafOfModules.unit (Proj 𝓑).ringCatSheaf ≅
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k := by
  apply nativeIntegerTwistWholeSheafIso 𝓑 a ha ?_ k
  intro p
  have h : p ∈ Proj.basicOpen 𝓑 a := by rw [htop]; trivial
  exact h

end LinearStudy