module
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeTwistRegradingMapNaturality
public import Linear.IntegerShiftedFreeRegradingPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
variable {K S I : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] (w : I → ℤ)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Regrading in degree0 is the SAME actual degree-k local-fraction predicate. -/
theorem nativeIntegerFreeTwistRegrading_predicate_iff (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := I → S) 𝓑 p.1) :
    (nativeProjectiveModuleLocalPredicate 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k)) 0).pred f ↔
      (nativeProjectiveModuleLocalPredicate 𝓑 (integerShiftedFreePiece 𝓑 w) k).pred f := by
  have hgrade : integerShiftedFreePiece 𝓑 (fun i => w i-k) =
      integerGradingShift (integerShiftedFreePiece 𝓑 w) k := by
    funext d
    exact integerShiftedFreePiece_regrade 𝓑 w k d
  rw [hgrade]
  exact nativeProjectiveTwistRegrading_predicate_iff 𝓑 (integerShiftedFreePiece 𝓑 w) k f


/-- The original localized values and ring action are unchanged on EVERY open. -/
def nativeIntegerFreeTwistRegradingSectionEquiv (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
      (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U where
  toFun x := ⟨x.1, (nativeIntegerFreeTwistRegrading_predicate_iff 𝓑 w k x.1).mp x.2⟩
  invFun x := ⟨x.1, (nativeIntegerFreeTwistRegrading_predicate_iff 𝓑 w k x.1).mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- This is identity on ACTUAL prime-localized values, not an abstract model equivalence. -/
theorem nativeIntegerFreeTwistRegradingSectionEquiv_value (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (x : nativeProjectiveModuleSections 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
      (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U) :
    (nativeIntegerFreeTwistRegradingSectionEquiv 𝓑 w k U x).1 = x.1 := rfl

/-- Actual O_Proj-linear regrading isomorphism, with actual restrictions.
This is not yet the comparison with a tensor-power Serre line bundle. -/
def nativeIntegerFreeTwistRegradingIso (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
      (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 ≅
        nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k where
  hom := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
        (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
        (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U
      exact ModuleCat.ofHom (nativeIntegerFreeTwistRegradingSectionEquiv 𝓑 w k U).toLinearMap
    naturality i := by apply ModuleCat.hom_ext; rfl } }
  inv := { val := {
    app U := by
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
        (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 (fun i => w i-k))
        (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) 0 U
      letI := nativeProjectiveModuleSectionGroup 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U
      letI := nativeProjectiveModuleSectionModule 𝓑 (integerShiftedFreePiece 𝓑 w) (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k U
      exact ModuleCat.ofHom (nativeIntegerFreeTwistRegradingSectionEquiv 𝓑 w k U).symm.toLinearMap
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


variable {M : Type} [AddCommGroup M] [Module K M] [Module S M]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ D d → b • x ∈ D ((n:ℤ)+d))
variable (β : (I → S) →ₗ[S] M)
variable (hβ : ∀ d : ℤ, ∀ x : I → S,
  x ∈ integerShiftedFreePiece 𝓑 w d → β x ∈ D d)

/-- The ORIGINAL beta square for EVERY integer k is proved on actual
localized values. Weights w-k,original beta and original native sheaves
are retained. This is the required primal bridge for all-k duality. -/
theorem nativeIntegerFreeTwistRegradingIso_quotient (k : ℤ) :
    (nativeIntegerFreeTwistRegradingIso 𝓑 w k).inv ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑
        (integerShiftedFreePiece 𝓑 (fun i => w i-k)) (integerGradingShift D k)
        (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k))
        (integerGradingShift_smul_homogeneous 𝓑 D hD k)
        β (integerShiftedFreeQuotient_regrade 𝓑 w D β hβ k) 0 ≫
      (nativeProjectiveTwistRegradingIso 𝓑 D hD k).hom =
    nativeProjectiveDegreeZeroSheafMap 𝓑 (integerShiftedFreePiece 𝓑 w) D
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) hD β hβ k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

end LinearStudy
