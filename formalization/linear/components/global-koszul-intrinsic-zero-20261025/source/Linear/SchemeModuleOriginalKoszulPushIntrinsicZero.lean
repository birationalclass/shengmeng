module
public import Linear.SchemeModuleOpenKoszulIntrinsicZero
public import Linear.SchemeModuleOriginalClassGlobalToLocal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalChainTopExtClassSmall schemeModuleGlobalToInternalExtAll
variable {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
variable (D : schemeModuleOpenKoszulChartData C (p+1))
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- For the SAME original epsilon built from its actual top-term iso,
the actual canonical local class of b_*epsilon vanishes EXACTLY when the
ORIGINAL coefficient morphism b pulls back to zero on the ORIGINAL cut.
The actual source iso is cancelled,not identified with a conventional
frame. Arbitrary quasicoherent N;no local freeness or faithful pullback. -/
theorem schemeModuleOriginalKoszulPush_intrinsic_zero_iff
    (hA : ∀ (N : X.Modules) (_ : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1)))
    {M N : X.Modules} [hN : N.IsQuasicoherent]
    (phi : C.X (p+1) ≅ M) (b : M ⟶ N) :
    letI := D.2.2.1
    letI := hAlpha
    letI := HasDerivedCategory.standard X.Modules
    (Scheme.Modules.restrictFunctor D.2.1).map
      (schemeModuleGlobalToInternalExtAll E N (p+1)
        ((schemeModuleOriginalChainTopExtClassSmall C (p+1) alpha hAlpha phi.hom
          (hAbove.eq_of_src _ _)).comp (Ext.mk₀ b) (add_zero _)))=0 ↔
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span (Set.range D.2.2.2.1)))))).map
            ((Scheme.Modules.restrictFunctor D.2.1).map b)=0 := by
  letI := D.2.2.1
  letI := hAlpha
  letI := HasDerivedCategory.standard X.Modules
  have hbase := schemeModuleOpenKoszulIntrinsicMapZeroProof C p D alpha hAlpha hAbove hA
  unfold schemeModuleOpenKoszulIntrinsicMapZeroStatement at hbase
  have h := hbase N hN (phi.hom ≫ b)
  have hz :
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range D.2.2.2.1)))))).map
          ((Scheme.Modules.restrictFunctor D.2.1).map (phi.hom ≫ b))=0 ↔
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range D.2.2.2.1)))))).map
          ((Scheme.Modules.restrictFunctor D.2.1).map b)=0 := by
    simp only [Functor.map_comp,Preadditive.IsIso.comp_left_eq_zero]
  have hp := schemeModuleOriginalChainTopExtClassSmall_comp_mk₀ C (p+1) alpha hAlpha
    phi.hom (hAbove.eq_of_src _ _) b
  have hleft := congrArg
    (fun z : Ext.{u} E N (p+1) =>
      (Scheme.Modules.restrictFunctor D.2.1).map
        (schemeModuleGlobalToInternalExtAll E N (p+1) z)) hp
  constructor
  · intro hzero
    exact (h.trans hz).mp (hleft.symm.trans hzero)
  · intro hzero
    exact hleft.trans ((h.trans hz).mpr hzero)
end LinearStudy
