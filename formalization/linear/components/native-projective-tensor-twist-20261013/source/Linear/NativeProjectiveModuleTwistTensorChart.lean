module
public import Linear.NativeProjectiveModuleTwistPairing
public import Linear.NativeStructureModuleSheaf
public import Mathlib.LinearAlgebra.TensorProduct.Associator
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
open scoped TensorProduct
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The local twist equivalence is multiplication by the original a^m. -/
theorem nativeProjectiveModulePrimeTwistEquiv_value
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (x : nativeProjectiveModuleAtPrime (D := M) 𝓑 p) :
    nativeProjectiveModulePrimeTwistEquiv 𝓑 p a ha m x = a^m • x := by
  induction x using LocalizedModule.induction_on with
  | _ ell b =>
    rw [nativeProjectiveModulePrimeTwistEquiv_mk, LocalizedModule.smul'_mk]

/-- The ring-frame map has the same actual value in the ring localization. -/
theorem nativeProjectiveModuleRingTwistEquiv_value
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (x : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p
      (nativeProjectiveModulePrimeTwistEquiv 𝓑 p a ha m x) =
    algebraMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl) (a^m) *
      nativeProjectiveRingModuleLocalizationEquiv 𝓑 p x := by
  induction x using LocalizedModule.induction_on with
  | _ ell b =>
    rw [nativeProjectiveModulePrimeTwistEquiv_mk,
      nativeProjectiveRingModuleLocalizationEquiv_mk,
      nativeProjectiveRingModuleLocalizationEquiv_mk]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

/-- The original structure-ring value is recovered exactly. -/
theorem nativeProjectiveTwistStructureValue
    (p : ProjectiveSpectrum 𝓑)
    (z : HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p z) = z.val := by
  exact (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).apply_symm_apply z.val

/-- Actual frame of the degree-m ring twist on every original a-chart subopen. -/
def nativeProjectiveModuleTwistRingFrameEquiv
    (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U := by
  let F : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U := {
    toFun c := ⟨fun p => nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (c.1 p)), by
      have h := nativeProjectiveModuleTwistLocalFraction_forward 𝓑
        (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑)
        a ha m 0 hp (nativeStructureRingZeroModuleSectionMap 𝓑 U c).property
      change (nativeProjectiveModuleLocalPredicate 𝓑
        (nativeProjectiveRingIntegerPiece 𝓑) ((0 : ℤ)+(m : ℤ))).pred
        (fun p => nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
          (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (c.1 p))) at h
      rw [Int.zero_add] at h
      convert h using 1 <;> rfl⟩
    map_add' c d := by
      apply Subtype.ext
      funext p
      change nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
        (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 ((c.1 p)+(d.1 p))) =
        nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
          (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (c.1 p)) +
        nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
          (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (d.1 p))
      rw [map_add, map_add]
    map_smul' c d := by
      apply Subtype.ext
      funext p
      change nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
        (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 ((c.1 p) • (d.1 p))) = _
      rw [(nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1).map_smul,
        (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).map_smul]
      rfl }
  apply LinearEquiv.ofBijective F
  constructor
  · intro c d h
    apply nativeStructureRingZeroModuleSectionMap_injective 𝓑 U
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).injective
      (congrArg (fun z => z.1 p) h)
  · intro f
    have hf : (nativeProjectiveModuleLocalPredicate 𝓑
        (nativeProjectiveRingIntegerPiece 𝓑) ((0 : ℤ)+(m : ℤ))).pred f.1 := by
      rw [Int.zero_add]
      convert f.property using 1 <;> rfl
    let g : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U :=
      ⟨fun p => (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f.1 p),
        nativeProjectiveModuleTwistLocalFraction_backward 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
          (nativeProjectiveRingIntegerPiece_graded 𝓑) a ha m 0 hp hf⟩
    refine ⟨(nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm g, ?_⟩
    apply Subtype.ext
    funext p
    have h := congrArg (fun z => z.1 p)
      ((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).apply_symm_apply g)
    change nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
      (((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm g).1 p) =
      (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f.1 p) at h
    change nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
        (((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm g).1 p)) = f.1 p
    rw [h, LinearEquiv.apply_symm_apply]

variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- The actual fraction pairing agrees with the actual local module frame. -/
theorem nativeProjectiveModuleTwistPairing_frame
    (a : S) (ha : a ∈ 𝓑 1) (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (c : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
    (ell : nativeProjectiveModuleSections 𝓑 𝒟 hD k U) :
    nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U
      (nativeProjectiveModuleTwistRingFrameEquiv 𝓑 a ha m U hp c) ell =
    nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k U hp (c • ell) := by
  apply Subtype.ext
  funext p
  change nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1
    (nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (c.1 p))) • ell.1 p =
    nativeProjectiveModulePrimeTwistEquiv 𝓑 p.1 a (hp p) m ((c.1 p) • ell.1 p)
  rw [nativeProjectiveModuleRingTwistEquiv_value, nativeProjectiveTwistStructureValue,
    nativeProjectiveModulePrimeTwistEquiv_value]
  change (algebraMap S (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) (a^m) *
    (c.1 p).val) • ell.1 p = a^m • ((c.1 p).val • ell.1 p)
  rw [mul_smul, algebraMap_smul]

/-- The actual sectionwise tensor has the constructed local twist isomorphism. -/
def nativeProjectiveModuleTwistTensorChartEquiv
    (a : S) (ha : a ∈ 𝓑 1) (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U ⊗[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD k U) ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD (k+(m : ℤ)) U :=
  ((TensorProduct.congr (nativeProjectiveModuleTwistRingFrameEquiv 𝓑 a ha m U hp).symm
      (LinearEquiv.refl _ _)).trans (TensorProduct.lid _ _)).trans
    (nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k U hp)

/-- The constructed chart tensor isomorphism is the original fraction pairing. -/
theorem nativeProjectiveModuleTwistTensorChartEquiv_eq_pairing
    (a : S) (ha : a ∈ 𝓑 1) (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (nativeProjectiveModuleTwistTensorChartEquiv 𝓑 𝒟 hD a ha m k U hp).toLinearMap =
      TensorProduct.lift (nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro ell
  change nativeProjectiveModuleTwistSectionEquiv 𝓑 𝒟 hD a ha m k U hp
    ((nativeProjectiveModuleTwistRingFrameEquiv 𝓑 a ha m U hp).symm r • ell) =
    nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U r ell
  have h := nativeProjectiveModuleTwistPairing_frame 𝓑 𝒟 hD a ha m k U hp
    ((nativeProjectiveModuleTwistRingFrameEquiv 𝓑 a ha m U hp).symm r) ell
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end LinearStudy
