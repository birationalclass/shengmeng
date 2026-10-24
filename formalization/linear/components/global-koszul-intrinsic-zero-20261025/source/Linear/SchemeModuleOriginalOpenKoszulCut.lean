module
public import Linear.SchemeModuleChainOpenKoszulHomCokernel
public import Linear.SchemeModuleOriginalWholeTopCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalWholeTopCokernelIso
  schemeModuleOriginalChainTopExtClassSmall schemeModuleGlobalToInternalExtAll
  schemeModuleChainOpenKoszulHomCokernelIso
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (p : ℕ) (H : Fin (p+1) → R) (C : ChainComplex X.Modules ℕ)
variable (gamma : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
  tildeFunctionKoszulComplex R H)
variable {E : X.Modules} (N : X.Modules) (T : ModuleCat.{u} R) (beta : N.restrict j ≅ tilde T)
variable (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
variable (I : InjectiveResolution N)
variable (hA : ∀ q v,IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
variable (hAbove : IsZero (C.X (p+2)))
/-- Compute the ACTUAL original INTERNAL SHEAF Ext on the SAME original Koszul chart. Every comparison is constructed from original source boundaries,actual open restriction and original geometric coefficient restriction. No MODULE Ext or desired comparison is assumed. -/
def schemeModuleOriginalOpenKoszulCutIso :
    (schemeModuleInternalExt E N (p+1)).restrict j ≅
      (affineKoszulHomGeometricRestrictionPresentation R T p H).X₃ :=
  (Scheme.Modules.restrictFunctor j).mapIso
      (schemeModuleOriginalWholeTopCokernelIso C N p alpha hAlpha I hA hAbove) ≪≫
    schemeModuleChainOpenKoszulHomCokernelIso R j p H C gamma N T beta
/-- SAME original global Ext class maps to SAME original framed functional on the SAME geometric cut. The native lambda map is used;no lambda-isomorphism assertion is made. The source top bound supplies closedness for every a. -/
theorem schemeModuleOriginalOpenKoszulCutIso_class (a : C.X (p+1) ⟶ N) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          (schemeModuleGlobalToInternalExtAll E N (p+1)
            (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
              (hAbove.eq_of_src (C.d (p+2) (p+1) ≫ a) 0))) ≫
        (schemeModuleOriginalOpenKoszulCutIso R j p H C gamma N T beta alpha hAlpha I hA hAbove).hom =
      (schemeModuleHomUnitAddEquiv _ (tilde T)).symm
          ((schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1)).inv ≫
            (Scheme.Modules.restrictFunctor j).map a ≫ beta.hom) ≫
        (affineKoszulHomGeometricRestrictionPresentation R T p H).g := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  have hc := schemeModuleOriginalSmallClass_wholeTopCokernel C p alpha hAlpha I hA hAbove a
    (hAbove.eq_of_src (C.d (p+2) (p+1) ≫ a) 0)
  have hc' := congrArg (fun z => (Scheme.Modules.restrictUnitIso j).inv ≫
    (Scheme.Modules.restrictFunctor j).map z ≫
      (schemeModuleChainOpenKoszulHomCokernelIso R j p H C gamma N T beta).hom) hc
  have hl := schemeModuleChainOpenKoszulHomCokernelIso_class R j p H C gamma N T beta a
  simpa only [schemeModuleOriginalOpenKoszulCutIso,Iso.trans_hom,Functor.mapIso_hom,
    Functor.map_comp,Category.assoc] using hc'.trans hl
end LinearStudy
