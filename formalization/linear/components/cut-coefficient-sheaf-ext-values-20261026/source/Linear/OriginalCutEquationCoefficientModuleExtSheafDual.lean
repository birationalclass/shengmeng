module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.KoszulOriginalModuleExtSheafValues
public import Linear.OriginalCutEquationCoefficientModuleExtDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- ACTUAL associated sheaf of derived MODULE Ext for the SAME original
ordered cut maps through actual pushforward/global sections to
native coextension on the SAME cut ring. Every original top functional
and polynomial value,including literal eval1,are retained. Statement only;
not derived SHEAF Ext,fixed original C_L or SAME geometric top-H. -/
def projectivePulledCutEquationCoefficientModuleExtSheafDualStatement {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ) : Prop :=
    let R := MvPolynomial (Fin (p+1)) ℂ
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let J := (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K:=ℂ)).toRingHom
    let Q := MvPolynomial (Fin n) ℂ ⧸ J
    let phi := projectivePulledCutEquationMap f V L w
    letI : Algebra R B := phi.toRingHom.toAlgebra
    letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
    letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
    letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin (p+1) → ℂ)).toRingHom.toAlgebra
    let D := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
    let Dq := (ModuleCat.coextendScalars (algebraMap ℂ Q)).obj (ModuleCat.of ℂ ℂ)
    let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
    let I := Ideal.span (Set.range H)
    let T := (ModuleCat.restrictScalars
      (projectivePulledCutOriginalRingMap f V L w).toRingHom).obj Dq
    koszulExactTopExtOriginalTwoSheafValuesStatement
      (CommRingCat.ofHom (projectivePulledCutOriginalRingMap f V L w).toRingHom) p H D Dq (MvPolynomial (Fin n) ℂ)
      (fun ell P z => (show Dq from z) (Ideal.Quotient.mk J P)=
        algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
            (Ideal.Quotient.mk V.affineIdeal P)))
      (fun ell z => (show Dq from z) (1:Q)=algebraMap R ℂ
        ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1))
/-- The SAME actual MODULE Ext comparison DERIVES its actual associated
sheaf comparison and every original representative/global-section value. -/
theorem projectivePulledCutEquation_moduleExt_sheaf_dual_of_moduleExt_dual {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ)
    (hmodule : projectivePulledCutEquationCoefficientModuleExtDualStatement f V L w) :
    projectivePulledCutEquationCoefficientModuleExtSheafDualStatement f V L w := by
  let R := MvPolynomial (Fin (p+1)) ℂ
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let J := (projectivePulledLinearSectionIdeal f V L w).map
    (affineChartPolynomialMap (K:=ℂ)).toRingHom
  let Q := MvPolynomial (Fin n) ℂ ⧸ J
  let phi := projectivePulledCutEquationMap f V L w
  letI : Algebra R B := phi.toRingHom.toAlgebra
  letI : SMul R B := phi.toRingHom.toAlgebra.toSMul
  letI : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
  letI : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin (p+1) → ℂ)).toRingHom.toAlgebra
  let D := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
  let Dq := (ModuleCat.coextendScalars (algebraMap ℂ Q)).obj (ModuleCat.of ℂ ℂ)
  let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
    (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
  let I := Ideal.span (Set.range H)
  let T := (ModuleCat.restrictScalars
    (projectivePulledCutOriginalRingMap f V L w).toRingHom).obj Dq
  exact koszulExactTopExtOriginalTwoSheafValuesStatement_of_moduleExt
    (CommRingCat.ofHom (projectivePulledCutOriginalRingMap f V L w).toRingHom) p H D Dq (MvPolynomial (Fin n) ℂ)
    (fun ell P z => (show Dq from z) (Ideal.Quotient.mk J P)=
      algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
          (Ideal.Quotient.mk V.affineIdeal P)))
    (fun ell z => (show Dq from z) (1:Q)=algebraMap R ℂ
      ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1)) hmodule
/-- FULL original Setup DERIVES actual associated MODULE Ext sheaf/native
cut duality and actual original global representative values on ONE
nonempty original open. No SHEAF Ext or fixed C_L comparison is assumed. -/
theorem projectivePulledCutEquation_originalSetup_exists_coefficient_moduleExt_sheaf_dual_open {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : p+1 < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin ((p+1)+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin ((p+1)+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin ((p+1)+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        (projectivePulledCutEquationMap f V L w).toRingHom.Finite ∧
        projectivePulledCutEquationCoefficientModuleExtSheafDualStatement f V L w := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledCutEquation_originalSetup_exists_coefficient_moduleExt_dual_open
    f V hrn hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  exact ⟨(hgood w hw).1,projectivePulledCutEquation_moduleExt_sheaf_dual_of_moduleExt_dual
    f V L w (hgood w hw).2⟩
end LinearStudy
