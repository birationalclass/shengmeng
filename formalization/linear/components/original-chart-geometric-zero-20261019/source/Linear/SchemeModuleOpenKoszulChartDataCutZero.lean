module
public import Linear.SchemeModuleOpenKoszulChartData
public import Linear.SchemeModuleOriginalOpenKoszulCutZero
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
/-- STATEMENT only:for every actual quasicoherent coefficient and original
functional,the SAME canonical lambda class restricts to zero iff its
actual ordered coefficient section pulls back to zero on the ORIGINAL
nonreduced scheme cut. No independent coordinate-frame choice is input. -/
def schemeModuleOpenKoszulChartDataCutZeroStatement : Prop :=
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  ∀ (N : X.Modules) (hN : N.IsQuasicoherent) (a : C.X (p+1) ⟶ N),
    letI := hN
    (Scheme.Modules.restrictFunctor D.2.1).map
        (schemeModuleGlobalToInternalExtAll E N (p+1)
          (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
            (hAbove.eq_of_src _ _))) = 0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span (Set.range D.2.2.2.1)))))).map
          (affineKoszulTopFunctionalSection D.1
            ((moduleSpecΓFunctor (R := D.1)).obj (N.restrict D.2.1)) p
            ((schemeModuleChainOpenKoszulTermIso D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2 (p+1)).inv ≫
              (Scheme.Modules.restrictFunctor D.2.1).map a ≫
                (schemeModuleOpenQuasicoherentCoefficientIso D.1 D.2.1 N).hom)) = 0
/-- Prove the actual all-coefficient criterion from source Ext acyclicity
and the actual chart class theorem. Original Koszul applications derive
that acyclicity and rank bound,so neither is a new geometric condition. -/
theorem schemeModuleOpenKoszulChartDataCutZeroProof
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1))) :
    schemeModuleOpenKoszulChartDataCutZeroStatement C p D alpha hAlpha hAbove := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  intro N hN a
  letI := hN
  exact schemeModuleOriginalOpenKoszulCutStatement_zero_iff
    D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2 N
    ((moduleSpecΓFunctor (R := D.1)).obj (N.restrict D.2.1))
    (schemeModuleOpenQuasicoherentCoefficientIso D.1 D.2.1 N)
    alpha hAlpha a (hAbove.eq_of_src _ _)
    (schemeModuleOriginalOpenKoszulQCCutStatement_proof
      D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2 alpha hAlpha hAbove hA N hN a)
end LinearStudy
