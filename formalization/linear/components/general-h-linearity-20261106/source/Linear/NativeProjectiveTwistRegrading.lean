module
public import Linear.IntegerGradingShift
public import Linear.NativeProjectiveModuleSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Regrading in degree0 is the SAME actual degree-k local-fraction predicate. -/
theorem nativeProjectiveTwistRegrading_predicate_iff (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (integerGradingShift 𝒟 k) 0).pred f ↔
      (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred f := by
  simp only [nativeProjectiveModuleLocalPredicate, PrelocalPredicate.sheafify,
    nativeProjectiveModuleFractionPrelocal, nativeProjectiveModuleIsFraction,
    integerGradingShift, add_zero]
  rfl

/-- The original localized values and ring action are unchanged on EVERY open. -/
def nativeProjectiveTwistRegradingSectionEquiv (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (integerGradingShift 𝒟 k)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD k U where
  toFun x := ⟨x.1, (nativeProjectiveTwistRegrading_predicate_iff 𝓑 𝒟 k x.1).mp x.2⟩
  invFun x := ⟨x.1, (nativeProjectiveTwistRegrading_predicate_iff 𝓑 𝒟 k x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- This is identity on ACTUAL prime-localized values, not an abstract model equivalence. -/
theorem nativeProjectiveTwistRegradingSectionEquiv_value (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (integerGradingShift 𝒟 k)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U) :
    (nativeProjectiveTwistRegradingSectionEquiv 𝓑 𝒟 hD k U x).1 = x.1 := rfl

/-- Actual O_Proj-linear regrading isomorphism, with actual restrictions.
This is not yet the comparison with a tensor-power Serre line bundle. -/
def nativeProjectiveTwistRegradingIso (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 (integerGradingShift 𝒟 k)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 ≅
        nativeProjectiveModuleSheaf 𝓑 𝒟 hD k where
  hom := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerGradingShift 𝒟 k)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerGradingShift 𝒟 k)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U
      letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD k U
      letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD k U
      exact ModuleCat.ofHom (nativeProjectiveTwistRegradingSectionEquiv 𝓑 𝒟 hD k U).toLinearMap
    naturality i := by apply ModuleCat.hom_ext; rfl } }
  inv := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerGradingShift 𝒟 k)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerGradingShift 𝒟 k)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD k) 0 U
      letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD k U
      letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD k U
      exact ModuleCat.ofHom (nativeProjectiveTwistRegradingSectionEquiv 𝓑 𝒟 hD k U).symm.toLinearMap
    naturality i := by apply ModuleCat.hom_ext; rfl } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
end LinearStudy
