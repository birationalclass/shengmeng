module
public import Linear.NativeSourceSpecOpenSectionsModule
public import Linear.NativeWeightedProjOpen
public import Linear.NativeProjectiveChartSections
public import Linear.OriginalProjectiveChartSectionRing
public import Linear.SchemeModuleSpecOpenNamedScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ,∀ d : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D d → c • x ∈ D ((n : ℤ)+d))
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap
/-- Scalar compatibility of the actual weighted section FUNCTION on the same
Spec open.No source Ai-module instance,linear-map repackaging,quasicoherence,
localization,domain or torsion-free assumption is required. -/
theorem nativeWeightedSpecSectionFunction_smul
    (e : ℕ) (he : 0 < e) (a b : S) (ha : a ∈ B 1) (hb : b ∈ B e)
    (r : HomogeneousLocalization.Away B a)
    (x : nativeGradedModuleAwayDegreeZero B D (1+e) (a*b)) :
    let F := nativeProjectiveModuleSheaf B D hD 0
    let j := Proj.awayι B a ha (by decide)
    let W : (Spec (CommRingCat.of (HomogeneousLocalization.Away B a))).Opens :=
      PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb)
    let E := schemeModuleSpecOpenSectionsEquiv F j W (Proj.basicOpen B (a*b))
      (nativeWeightedProjRatioOpen_image B e he a b ha hb)
    let q := nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (a*b)
      (SetLike.mul_mem_graded ha hb)
    let rho := HomogeneousLocalization.awayMap B hb (rfl : a*b=a*b)
    letI := nativeSourceSpecOpenSectionsModule B D hD a ha W
    E (q (rho r • x)) = r • E (q x) := by
  let F := nativeProjectiveModuleSheaf B D hD 0
  let j := Proj.awayι B a ha (by decide)
  let W : (Spec (CommRingCat.of (HomogeneousLocalization.Away B a))).Opens :=
    PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb)
  let U := Proj.basicOpen B (a*b)
  letI := nativeSourceSpecOpenSectionsModule B D hD a ha W
  have hW : j ''ᵁ W = U := nativeWeightedProjRatioOpen_image B e he a b ha hb
  have hT : j ''ᵁ ⊤ = Proj.basicOpen B a :=
    j.image_top_eq_opensRange.trans (Proj.opensRange_awayι B a ha (by decide))
  let E := schemeModuleSpecOpenSectionsEquiv F j W U hW
  let q := nativeProjectiveChartDegreeZeroSectionMap B D hD (1+e) (a*b)
    (SetLike.mul_mem_graded ha hb)
  let rho := HomogeneousLocalization.awayMap B hb (rfl : a*b=a*b)
  have hphi : Proj.awayToSection B a ≫ (Proj B).presheaf.map (eqToHom hT).op ≫
      (j.appIso ⊤).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away B a))).inv := by
    have hh : (Proj B).presheaf.map (eqToHom hT).op ≫ (j.appIso ⊤).hom =
        j.appLE (Proj.basicOpen B a) ⊤ (by rw [←hT]; exact (j.preimage_image_eq ⊤).ge) := by
      rw [Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE']
    rw [hh]
    exact originalProjectiveChartScalar_appLE B a ha
  change E (q (rho r • x)) = r • E (q x)
  rw [q.map_smulₛₗ]
  have hr : (Proj.awayToSection B (a*b)).hom (rho r) =
      (Proj B).presheaf.map (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left B a b)).op
        (Proj.awayToSection B a r) := by
    have H : CommRingCat.ofHom rho ≫ Proj.awayToSection B (a*b) =
        Proj.awayToSection B a ≫ (Proj B).presheaf.map
          (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left B a b)).op :=
      Proj.awayMap_awayToSection B hb (rfl : a*b=a*b)
    convert! congr($(H).hom r) using 1 <;> rfl
  have H := schemeModuleSpecOpenSectionsEquiv_smul_namedImages F j W U (Proj.basicOpen B a)
    hW hT (Proj.awayToSection B a) hphi r (q x)
  exact (congrArg (fun c => E (c • q x)) hr).trans H
end LinearStudy
