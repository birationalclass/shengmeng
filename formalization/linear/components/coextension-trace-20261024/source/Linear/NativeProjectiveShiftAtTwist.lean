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

/-- For EVERY original integer twist k, regrading D by delta gives the SAME actual local-fraction predicate in degree k+delta. -/
theorem nativeProjectiveShiftAtTwist_predicate_iff (δ k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := M) 𝓑 p.1) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (integerGradingShift 𝒟 δ) k).pred f ↔
      (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 (k+δ)).pred f := by
  constructor
  · intro hf p
    rcases hf p with ⟨V,hp,i,hf⟩
    rcases hf with ⟨n,ell,b,hb,hf⟩
    refine ⟨V,hp,i,n,⟨(ell : M),?_⟩,b,hb,hf⟩
    simpa only [integerGradingShift,add_assoc] using ell.property
  · intro hf p
    rcases hf p with ⟨V,hp,i,hf⟩
    rcases hf with ⟨n,ell,b,hb,hf⟩
    refine ⟨V,hp,i,n,⟨(ell : M),?_⟩,b,hb,hf⟩
    simpa only [integerGradingShift,add_assoc] using ell.property

/-- The original localized values and ring action are unchanged on EVERY open. -/
def nativeProjectiveShiftAtTwistSectionEquiv (δ k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (integerGradingShift 𝒟 δ)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD (k+δ) U where
  toFun x := ⟨x.1, (nativeProjectiveShiftAtTwist_predicate_iff 𝓑 𝒟 δ k x.1).mp x.2⟩
  invFun x := ⟨x.1, (nativeProjectiveShiftAtTwist_predicate_iff 𝓑 𝒟 δ k x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- This is identity on ACTUAL prime-localized values, not an abstract model equivalence. -/
theorem nativeProjectiveShiftAtTwistSectionEquiv_value (δ k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (integerGradingShift 𝒟 δ)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U) :
    (nativeProjectiveShiftAtTwistSectionEquiv 𝓑 𝒟 hD δ k U x).1 = x.1 := rfl

/-- Actual O_Proj-linear regrading isomorphism, with actual restrictions.
The same original prime-localized values are retained for ALL integers delta and k; the Serre tensor-line-bundle comparison remains separate. -/
def nativeProjectiveShiftAtTwistIso (δ k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 (integerGradingShift 𝒟 δ)
      (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k ≅
        nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+δ) where
  hom := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerGradingShift 𝒟 δ)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerGradingShift 𝒟 δ)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U
      letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD (k+δ) U
      letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD (k+δ) U
      exact ModuleCat.ofHom (nativeProjectiveShiftAtTwistSectionEquiv 𝓑 𝒟 hD δ k U).toLinearMap
    naturality i := by apply ModuleCat.hom_ext; rfl } }
  inv := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerGradingShift 𝒟 δ)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerGradingShift 𝒟 δ)
        (integerGradingShift_smul_homogeneous 𝓑 𝒟 hD δ) k U
      letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD (k+δ) U
      letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD (k+δ) U
      exact ModuleCat.ofHom (nativeProjectiveShiftAtTwistSectionEquiv 𝓑 𝒟 hD δ k U).symm.toLinearMap
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
