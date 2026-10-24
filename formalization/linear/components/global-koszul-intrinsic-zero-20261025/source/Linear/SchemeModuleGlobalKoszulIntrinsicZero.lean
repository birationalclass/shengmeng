module
public import Linear.SchemeModuleOriginalKoszulPushIntrinsicZero
public import Linear.SchemeModuleGlobalExtOpenZero
public import Linear.SchemeModuleChartInternalExtSupport
public import Linear.SchemeModuleFiniteSupportLambdaSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalChainTopExtClassSmall schemeModuleGlobalToInternalExtAll
variable {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
variable (D : schemeModuleOpenKoszulChartData C (p+1))
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- Statement only:the SAME GLOBAL original Ext class vanishes iff the
ORIGINAL top coefficient morphism has zero ACTUAL cut pullback. -/
def schemeModuleGlobalKoszulIntrinsicZeroStatement : Prop :=
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  ∀ (N : X.Modules) (_ : N.IsQuasicoherent) (a : C.X (p+1) ⟶ N),
    schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
      (hAbove.eq_of_src _ _)=0 ↔
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range D.2.2.2.1)))))).map
          ((Scheme.Modules.restrictFunctor D.2.1).map a)=0
/-- SAME canonical lambda and actual target-support unit detect GLOBAL
vanishing. Explicit generic input laws are derived from original
finite-cut geometry in the projective family. -/
theorem schemeModuleGlobalKoszulIntrinsicZeroProof
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
    (hLambda : ∀ N,Function.Injective (schemeModuleGlobalToInternalExt E N p))
    (hUnit : letI := D.2.2.1
      ∀ N,IsIso ((Scheme.Modules.restrictAdjunction D.2.1).unit.app
        (schemeModuleInternalExt E N (p+1)))) :
    schemeModuleGlobalKoszulIntrinsicZeroStatement C p D alpha hAlpha hAbove := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  intro N hN a
  have h := schemeModuleOpenKoszulIntrinsicMapZeroProof C p D alpha hAlpha hAbove hA
  unfold schemeModuleOpenKoszulIntrinsicMapZeroStatement at h
  exact (schemeModuleGlobalExt_zero_iff_open D.2.1 E N p (hLambda N) (hUnit N)
    (schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha a
      (hAbove.eq_of_src _ _))).trans (h N hN a)
/-- Derive target-lambda injectivity from the SAME actual cokernel iso;
actual original cover will derive support. No class-law field is input. -/
theorem schemeModuleGlobalKoszulIntrinsicZeroProof_of_cokernelLambda
    (e : cokernel (C.d 1 0) ≅ E)
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
    (hLambda : ∀ N,Function.Bijective
      (schemeModuleGlobalToInternalExt (cokernel (C.d 1 0)) N p))
    (hSupport : schemeModuleChartInternalExtSupportStatement C (p+1) D E) :
    schemeModuleGlobalKoszulIntrinsicZeroStatement C p D alpha hAlpha hAbove := by
  apply schemeModuleGlobalKoszulIntrinsicZeroProof C p D alpha hAlpha hAbove hA
  · intro N
    exact (schemeModuleGlobalToInternalExt_bijective_of_sourceIso e.symm N p (hLambda N)).injective
  · intro N
    exact hSupport N (p+1)
/-- The SAME GLOBAL b_*epsilon,with actual source iso cancelled after
actual pullback. No target frame,faithful pullback or new trace input. -/
theorem schemeModuleOriginalKoszulPush_global_intrinsic_zero_iff
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
    (hLambda : ∀ N,Function.Injective (schemeModuleGlobalToInternalExt E N p))
    (hUnit : letI := D.2.2.1
      ∀ N,IsIso ((Scheme.Modules.restrictAdjunction D.2.1).unit.app
        (schemeModuleInternalExt E N (p+1))))
    {M N : X.Modules} [N.IsQuasicoherent]
    (phi : C.X (p+1) ≅ M) (b : M ⟶ N) :
    letI := D.2.2.1
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    ((schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha phi.hom
      (hAbove.eq_of_src _ _)).comp (Ext.mk₀ b) (add_zero _))=0 ↔
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range D.2.2.2.1)))))).map
          ((Scheme.Modules.restrictFunctor D.2.1).map b)=0 := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  exact (schemeModuleGlobalExt_zero_iff_open D.2.1 E N p (hLambda N) (hUnit N)
    ((schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha phi.hom
      (hAbove.eq_of_src _ _)).comp (Ext.mk₀ b) (add_zero _))).trans
    (schemeModuleOriginalKoszulPush_intrinsic_zero_iff C p D alpha hAlpha hAbove hA phi b)
end LinearStudy
