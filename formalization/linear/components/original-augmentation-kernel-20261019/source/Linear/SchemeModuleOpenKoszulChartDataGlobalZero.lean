module
public import Linear.SchemeModuleOpenKoszulChartDataCutZero
public import Linear.SchemeModuleGlobalExtOpenZero
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
variable {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
variable (D : schemeModuleOpenKoszulChartData C (p+1))
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- Statement only:the ACTUAL GLOBAL original Ext class vanishes iff its
actual ordered coefficient section has zero pullback on the ORIGINAL
nonreduced cut. This strengthens the previously LOCAL class criterion. -/
def schemeModuleOpenKoszulChartDataGlobalZeroStatement : Prop :=
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  ∀ (N : X.Modules) (hN : N.IsQuasicoherent) (a : C.X (p+1) ⟶ N),
    letI := hN
    schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
      (hAbove.eq_of_src _ _) = 0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span (Set.range D.2.2.2.1)))))).map
          (affineKoszulTopFunctionalSection D.1
            ((moduleSpecΓFunctor (R := D.1)).obj (N.restrict D.2.1)) p
            ((schemeModuleChainOpenKoszulTermIso D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2 (p+1)).inv ≫
              (Scheme.Modules.restrictFunctor D.2.1).map a ≫
                (schemeModuleOpenQuasicoherentCoefficientIso D.1 D.2.1 N).hom)) = 0
/-- Actual global detection,using the SAME canonical lambda and SAME
actual restriction unit. Original finite-cut geometry derives their
injectivity and support;neither conclusion is a final geometric premise. -/
theorem schemeModuleOpenKoszulChartDataGlobalZeroProof
    (hLocal : schemeModuleOpenKoszulChartDataCutZeroStatement C p D alpha hAlpha hAbove)
    (hLambda : ∀ N,Function.Injective (schemeModuleGlobalToInternalExt E N p))
    (hUnit : letI := D.2.2.1
      ∀ N,IsIso ((Scheme.Modules.restrictAdjunction D.2.1).unit.app
        (schemeModuleInternalExt E N (p+1)))) :
    schemeModuleOpenKoszulChartDataGlobalZeroStatement C p D alpha hAlpha hAbove := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  intro N hN a
  letI := hN
  exact (schemeModuleGlobalExt_zero_iff_open D.2.1 E N p (hLambda N) (hUnit N)
    (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
      (hAbove.eq_of_src _ _))).trans (hLocal N hN a)
end LinearStudy
