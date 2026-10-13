module
public import Linear.NativeProjectiveModuleTwistSectionEquiv
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)

/-- Restricting to the actual open U on which a is nonvanishing gives
a genuine isomorphism of associated-module presheaves on the native
over-site, including all structure-ring actions and restriction maps. -/
def nativeProjectiveModuleTwistPresheafOverIso (k : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    ((nativeProjectiveModuleSheaf 𝓑 𝒟
      hD k).over U).val ≅
      ((nativeProjectiveModuleSheaf 𝓑 𝒟
        hD (k+(m : ℤ))).over U).val :=
  PresheafOfModules.isoMk (fun Z => by
    let V := op Z.unop.left
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟
      hD k V
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟
      hD k V
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟
      hD (k+(m : ℤ)) V
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟
      hD (k+(m : ℤ)) V
    exact (nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k V
      (fun p => hp (Z.unop.hom p))).toModuleIso)
    (by intros; apply ModuleCat.hom_ext; rfl)

/-- Genuine local trivialization of the actual positive homogeneous
twist SHEAF on the original native over-site, obtained from proved
section formulas and their naturality, with no sheaf isomorphism input. -/
def nativeProjectiveModuleTwistSheafOverIso (k : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝓑))
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟
      hD k).over U ≅
      (nativeProjectiveModuleSheaf 𝓑 𝒟
        hD (k+(m : ℤ))).over U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (nativeProjectiveModuleTwistPresheafOverIso 𝓑 𝒟 hD a ha m k U hp)

end LinearStudy
