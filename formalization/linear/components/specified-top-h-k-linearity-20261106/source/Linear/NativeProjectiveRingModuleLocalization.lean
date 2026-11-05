module
public import Linear.NativeProjectiveRingIntegerPieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- The localization of the original ring as a MODULE is the actual
ring localization, with the native homogeneous local-ring action. -/
def nativeProjectiveRingModuleLocalizationEquiv (p : ProjectiveSpectrum 𝓑) :
    nativeProjectiveModuleAtPrime (D := S) 𝓑 p ≃ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      Localization p.asHomogeneousIdeal.toIdeal.primeCompl := by
  let T := Localization p.asHomogeneousIdeal.toIdeal.primeCompl
  let e := (IsLocalizedModule.iso p.asHomogeneousIdeal.toIdeal.primeCompl
    (Algebra.linearMap S T)).extendScalarsOfIsLocalization
      p.asHomogeneousIdeal.toIdeal.primeCompl T
  exact {
    toEquiv := e.toEquiv
    map_add' := e.map_add
    map_smul' := fun z x => e.map_smul (algebraMap _ T z) x }

theorem nativeProjectiveRingModuleLocalizationEquiv_mk
    (p : ProjectiveSpectrum 𝓑) (x : S)
    (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p (LocalizedModule.mk x b) =
      IsLocalization.mk' (Localization p.asHomogeneousIdeal.toIdeal.primeCompl) x b := by
  change IsLocalizedModule.mk'
    (Algebra.linearMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)) x b = _
  exact (IsLocalization.mk'_eq_mk' p.asHomogeneousIdeal.toIdeal.primeCompl
    (Localization p.asHomogeneousIdeal.toIdeal.primeCompl) x b).symm

/-- Embed the ACTUAL native homogeneous local ring into the original
ring-module localization, for comparison with its degree-zero sheaf. -/
def nativeHomogeneousLocalRingModuleEmbedding (p : ProjectiveSpectrum 𝓑) :
    HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal →ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      nativeProjectiveModuleAtPrime (D := S) 𝓑 p where
  toFun z := (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm z.val
  map_add' x y := by simp only [HomogeneousLocalization.val_add,map_add]
  map_smul' r x := by
    change (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm (r*x).val = _
    rw [HomogeneousLocalization.val_mul]
    exact (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm.map_smul r x.val

theorem nativeHomogeneousLocalRingModuleEmbedding_injective (p : ProjectiveSpectrum 𝓑) :
    Function.Injective (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p) :=
  (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm.injective.comp
    (HomogeneousLocalization.val_injective p.asHomogeneousIdeal.toIdeal.primeCompl)

theorem nativeHomogeneousLocalRingModuleEmbedding_mk
    (p : ProjectiveSpectrum 𝓑) (n : ℕ) (a b : 𝓑 n)
    (hb : (b : S) ∉ p.asHomogeneousIdeal) :
    nativeHomogeneousLocalRingModuleEmbedding 𝓑 p
      (HomogeneousLocalization.mk ⟨n,a,b,hb⟩) =
      LocalizedModule.mk (a : S) ⟨(b : S),hb⟩ := by
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).injective
  change (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p)
    ((nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm
      (HomogeneousLocalization.mk ⟨n,a,b,hb⟩ :
        HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal).val) = _
  rw [LinearEquiv.apply_symm_apply,nativeProjectiveRingModuleLocalizationEquiv_mk]
  rw [HomogeneousLocalization.val_mk,Localization.mk_eq_mk']

end LinearStudy
