module
public import Linear.SchemeModuleOriginalOpenKoszulCutStatement
public import Linear.AffineKoszulGeometricClassZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalChainTopExtClassSmall schemeModuleGlobalToInternalExtAll
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (p : ℕ) (H : Fin (p+1) → R) (C : ChainComplex X.Modules ℕ)
variable (gamma : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
  tildeFunctionKoszulComplex R H)
variable {E : X.Modules} (N : X.Modules) (T : ModuleCat.{u} R) (beta : N.restrict j ≅ tilde T)
variable (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
/-- The proved ACTUAL local class formula gives an intrinsic geometric
zero criterion:the restricted canonical lambda class is zero iff its
SAME actual ordered coefficient section pulls back to zero on the ORIGINAL
nonreduced scheme cut. Neither faithful pullback nor a sign comparison
with an independently prescribed frame is needed for this criterion. -/
theorem schemeModuleOriginalOpenKoszulCutStatement_zero_iff
    (a : C.X (p+1) ⟶ N) (ha : C.d (p+2) (p+1) ≫ a = 0)
    (h : schemeModuleOriginalOpenKoszulCutStatement R j p H C gamma N T beta alpha hAlpha a ha) :
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    (Scheme.Modules.restrictFunctor j).map
        (schemeModuleGlobalToInternalExtAll E N (p+1)
          (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a ha)) = 0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).map
          (affineKoszulTopFunctionalSection R T p
            ((schemeModuleChainOpenKoszulTermIso R j p H C gamma (p+1)).inv ≫
              (Scheme.Modules.restrictFunctor j).map a ≫ beta.hom)) = 0 := by
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  obtain ⟨chi,hchi⟩ := h
  rw [← affineKoszulGeometricClass_zero_iff_pullback R T p H]
  rw [← hchi]
  constructor
  · intro hz
    simp only [hz,comp_zero,zero_comp]
  · intro hz
    apply (cancel_mono chi.hom).mp
    apply (cancel_epi (Scheme.Modules.restrictUnitIso j).inv).mp
    simpa only [Category.assoc,comp_zero,zero_comp] using hz
end LinearStudy
