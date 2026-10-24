module
public import Linear.SchemeModuleOpenKoszulChartDataCutZero
public import Linear.AffineKoszulIntrinsicPullbackZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalChainTopExtClassSmall schemeModuleGlobalToInternalExtAll
variable {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
variable (D : schemeModuleOpenKoszulChartData C (p+1))
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- STATEMENT,not a proof:the SAME canonical local Ext class vanishes
iff the ORIGINAL top functional itself pulls back to zero on the SAME
original nonreduced cut. No replacement coefficient section occurs in
the conclusion,no coefficient/conventional frame is supplied as input. -/
def schemeModuleOpenKoszulIntrinsicMapZeroStatement : Prop :=
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  ∀ (N : X.Modules) (_ : N.IsQuasicoherent) (a : C.X (p+1) ⟶ N),
    (Scheme.Modules.restrictFunctor D.2.1).map
      (schemeModuleGlobalToInternalExtAll E N (p+1)
        (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
          (hAbove.eq_of_src _ _)))=0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span (Set.range D.2.2.2.1)))))).map
            ((Scheme.Modules.restrictFunctor D.2.1).map a)=0
/-- PROVE the intrinsic criterion using the ACTUAL original class
formula and ACTUAL source/target isomorphisms. Original source internal
Ext acyclicity is explicit here and is DERIVED for the original projective
Koszul complex;no global CM or target locally-free hypothesis. -/
theorem schemeModuleOpenKoszulIntrinsicMapZeroProof
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1))) :
    schemeModuleOpenKoszulIntrinsicMapZeroStatement C p D alpha hAlpha hAbove := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  intro N hN a
  letI := hN
  let T := (moduleSpecΓFunctor (R:=D.1)).obj (N.restrict D.2.1)
  let beta := schemeModuleOpenQuasicoherentCoefficientIso D.1 D.2.1 N
  let s := schemeModuleChainOpenKoszulTermIso D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2 (p+1)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range D.2.2.2.1))))
  let F := Scheme.Modules.pullback i
  have h := schemeModuleOpenKoszulChartDataCutZeroProof C p D alpha hAlpha hAbove hA N hN a
  have haff := affineKoszulTopFunctionalSection_pullback_zero_iff D.1 T p i
    (s.inv ≫ (Scheme.Modules.restrictFunctor D.2.1).map a ≫ beta.hom)
  refine h.trans (haff.trans ?_)
  change F.map (s.inv ≫ (Scheme.Modules.restrictFunctor D.2.1).map a ≫ beta.hom)=0 ↔
    F.map ((Scheme.Modules.restrictFunctor D.2.1).map a)=0
  simp only [F.map_comp,Preadditive.IsIso.comp_left_eq_zero,Preadditive.IsIso.comp_right_eq_zero]
end LinearStudy
