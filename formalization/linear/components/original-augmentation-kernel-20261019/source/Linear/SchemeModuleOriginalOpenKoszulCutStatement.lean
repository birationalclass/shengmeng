module
public import Linear.SchemeModuleOriginalOpenKoszulCut
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
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (p : ℕ) (H : Fin (p+1) → R) (C : ChainComplex X.Modules ℕ)
variable (gamma : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
  tildeFunctionKoszulComplex R H)
variable {E : X.Modules} (N : X.Modules) (T : ModuleCat.{u} R) (beta : N.restrict j ≅ tilde T)
variable (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
/-- Explicit class-image STATEMENT for SAME original objects. This Prop definition is not itself a proof. The required actual comparison is an existential conclusion,never a supplied certificate. -/
def schemeModuleOriginalOpenKoszulCutStatement (a : C.X (p+1) ⟶ N)
    (ha : C.d (p+2) (p+1) ≫ a = 0) : Prop :=
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  ∃ chi : (schemeModuleInternalExt E N (p+1)).restrict j ≅
      (affineKoszulHomGeometricRestrictionPresentation R T p H).X₃,
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          (schemeModuleGlobalToInternalExtAll E N (p+1)
            (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a ha)) ≫ chi.hom =
      (schemeModuleHomUnitAddEquiv _ (tilde T)).symm
          ((schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1)).inv ≫
            (Scheme.Modules.restrictFunctor j).map a ≫ beta.hom) ≫
        (affineKoszulHomGeometricRestrictionPresentation R T p H).g
/-- PROVE the statement from source internal-Ext acyclicity and top bound,using the actual original comparison. Both inputs will be derived in the geometric specialization. -/
theorem schemeModuleOriginalOpenKoszulCutStatement_proof
    (I : InjectiveResolution N)
    (hA : ∀ q v,IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
    (hAbove : IsZero (C.X (p+2)))
    (a : C.X (p+1) ⟶ N) (ha : C.d (p+2) (p+1) ≫ a = 0) :
    schemeModuleOriginalOpenKoszulCutStatement R j p H C gamma N T beta alpha hAlpha a ha := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  refine ⟨schemeModuleOriginalOpenKoszulCutIso R j p H C gamma N T beta alpha hAlpha I hA hAbove,?_⟩
  exact schemeModuleOriginalOpenKoszulCutIso_class R j p H C gamma N T beta alpha hAlpha I hA hAbove a
end LinearStudy
