module
public import Linear.AffineKoszulOriginalSheafExtClass
public import Linear.TildeCoefficientQuotientGeometricUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local irreducible] schemeModuleHomPrecompose schemeModuleHomModuleSheaf
  affineTildeTensorPullbackIso tildeCoefficientQuotientPushforwardIso
  tildeCoefficientQuotientGeometricPullbackPushforwardIso
/-- SAME ordered top functional goes to its ORIGINAL coefficient quotient,
using the actual Hom/tilde comparison and actual coefficient restriction. -/
def affineKoszulOriginalTopCoefficientQuotientMap (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    schemeModuleHomModuleSheaf (X:=Spec R)
      (tilde (ModuleCat.of R (⋀[R]^(p+1) (Fin (p+1) → R)))) (tilde N) ⟶
      tilde (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) :=
  (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).inv ≫
    (tilde.functor R).map (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N:=N) p H))
/-- First retain SAME actual quotient-tensor presentation. Its third
component is related to the original quotient without unfolding pullback. -/
theorem affineKoszulHomCoefficientRestriction_eq_originalQuotient (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    (affineKoszulHomCoefficientRestrictionPresentation R N p H).g =
      affineKoszulOriginalTopCoefficientQuotientMap R N p H ≫
        (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom := by
  exact (Category.assoc (affineKoszulTermHomCoefficientIso R N (p+1) (p+1)).inv
    ((tilde.functor R).map (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N:=N) p H)))
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom).symm
/-- Use mathlib's third projection of the ALREADY constructed original
short-complex iso. Its exact codomain is the actual original geometry;
no conversion between concrete pullback constructors is required. -/
def affineKoszulOriginalCoefficientTensorGeometricIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    (affineKoszulHomCoefficientRestrictionPresentation R N p H).X₃ ≅
      (affineKoszulHomGeometricRestrictionPresentation R N p H).X₃ :=
  ShortComplex.π₃.mapIso (affineKoszulHomGeometricRestrictionPresentationIso R N p H)
/-- The existing whole-short-complex morphism PROVES the actual quotient
restriction square. The second component is literally the identity. -/
theorem affineKoszulOriginalCoefficientTensorGeometricIso_restriction (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R) :
    (affineKoszulHomCoefficientRestrictionPresentation R N p H).g ≫
        (affineKoszulOriginalCoefficientTensorGeometricIso R N p H).hom =
      (affineKoszulHomGeometricRestrictionPresentation R N p H).g := by
  let e := affineKoszulHomGeometricRestrictionPresentationIso R N p H
  have h₂ : e.hom.τ₂ = 𝟙 _ := rfl
  change (affineKoszulHomCoefficientRestrictionPresentation R N p H).g ≫ e.hom.τ₃ = _
  rw [← e.hom.comm₂₃,h₂,Category.id_comp]
/-- Actual derived SHEAF Ext to SAME quotient-tensor coefficient,using
only the actual third component of the proved original complex iso. -/
def affineKoszulOriginalSheafExtTensorIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      (affineKoszulHomCoefficientRestrictionPresentation R N p H).X₃ :=
  affineKoszulOriginalSheafExtGeometricIso R N p H he I ≪≫
    (affineKoszulOriginalCoefficientTensorGeometricIso R N p H).symm
/-- SAME original class law for SAME original quotient-tensor restriction. -/
theorem affineKoszulOriginalSheafExtTensorIso_classLaw (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H))
      (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
      (affineKoszulOriginalSheafExtTensorIso R N p H he I)
      (affineKoszulHomCoefficientRestrictionPresentation R N p H).g := by
  have h := schemeModuleOriginalTopExtClassIsoLaw_postcompose
    (tildeFunctionKoszulComplex R H) (p+1)
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
    (affineKoszulOriginalSheafExtGeometricIso R N p H he I)
    (affineKoszulHomGeometricRestrictionPresentation R N p H).g
    (affineKoszulOriginalSheafExtGeometricIso_classLaw R N p H he I)
    (affineKoszulOriginalCoefficientTensorGeometricIso R N p H).symm
  rw [← affineKoszulOriginalCoefficientTensorGeometricIso_restriction] at h
  simpa only [affineKoszulOriginalSheafExtTensorIso,Iso.symm_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id] using h
/-- ACTUAL derived SHEAF Ext to SAME original coefficient quotient. -/
def affineKoszulOriginalSheafExtQuotientIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleInternalExt (tildeKoszulOriginalCutCokernelCofork R H).pt (tilde N) (p+1) ≅
      tilde (ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))) :=
  affineKoszulOriginalSheafExtTensorIso R N p H he I ≪≫
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).symm
/-- ALL SAME original roof classes under actual canonical lambda retain
SAME ordered-top coefficient quotient,uniformly for one constructed iso. -/
theorem affineKoszulOriginalSheafExtQuotientIso_classLaw (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (p : ℕ) (H : Fin (p+1) → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (I : InjectiveResolution (tilde N)) :
    schemeModuleOriginalTopExtClassIsoLaw (tildeFunctionKoszulComplex R H) (p+1)
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H))
      (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
      (affineKoszulOriginalSheafExtQuotientIso R N p H he I)
      (affineKoszulOriginalTopCoefficientQuotientMap R N p H) := by
  have h := schemeModuleOriginalTopExtClassIsoLaw_postcompose
    (tildeFunctionKoszulComplex R H) (p+1)
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))
    (tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he)
    (affineKoszulOriginalSheafExtTensorIso R N p H he I)
    (affineKoszulHomCoefficientRestrictionPresentation R N p H).g
    (affineKoszulOriginalSheafExtTensorIso_classLaw R N p H he I)
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).symm
  rw [affineKoszulHomCoefficientRestriction_eq_originalQuotient] at h
  simpa only [affineKoszulOriginalSheafExtQuotientIso,Iso.symm_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id] using h
end LinearStudy
