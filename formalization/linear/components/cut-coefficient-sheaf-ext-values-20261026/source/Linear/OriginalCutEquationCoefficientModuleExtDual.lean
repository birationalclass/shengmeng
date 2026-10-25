module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.KoszulNativeCoextensionOriginalValues
public import Linear.ProjectiveCutAffineKoszul
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
/-- ACTUAL derived MODULE Ext for the SAME original ordered cut maps to
native coextension on the SAME cut ring. Every original top functional
and polynomial value,including literal eval1,are retained. Statement only;
not derived SHEAF Ext,fixed original C_L or SAME geometric top-H. -/
def projectivePulledCutEquationCoefficientModuleExtDualStatement {n p : ℕ}
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
    koszulExactTopExtOriginalTwoValuesStatement p H D T (MvPolynomial (Fin n) ℂ)
      (fun ell P z => (show Dq from z) (Ideal.Quotient.mk J P)=
        algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
            (Ideal.Quotient.mk V.affineIdeal P)))
      (fun ell z => (show Dq from z) (1:Q)=algebraMap R ℂ
        ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1))
/-- The ACTUAL original native coefficient quotient duality and SAME
source Koszul exactness DERIVE the actual MODULE Ext/value comparison. -/
theorem projectivePulledCutEquation_moduleExt_dual_of_native_dual {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ)
    (he : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
      ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination B H)).ExactAt j)
    (hdual : projectivePulledCutEquationCoefficientNativeDualStatement f V L w) :
    projectivePulledCutEquationCoefficientModuleExtDualStatement f V L w := by
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
  exact koszulExactTopExtOriginalTwoValuesStatement_of_coefficient p H he D T (MvPolynomial (Fin n) ℂ)
    (fun ell P z => (show Dq from z) (Ideal.Quotient.mk J P)=
      algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
          (Ideal.Quotient.mk V.affineIdeal P)))
    (fun ell z => (show Dq from z) (1:Q)=algebraMap R ℂ
      ((coextensionOriginalDualEquiv (R:=R) (S:=B)
        (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1)) hdual
/-- FULL original Setup DERIVES the SAME nonempty open with actual source
exactness and actual native MODULE Ext duality,for original positive rank
r=p+1. No coefficient dual or exactness premise is added to Setup. -/
theorem projectivePulledCutEquation_originalSetup_exists_coefficient_moduleExt_dual_open {n p : ℕ}
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
        projectivePulledCutEquationCoefficientModuleExtDualStatement f V L w := by
  obtain ⟨a,ha,_,hdual⟩ := projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open
    f V hrn hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨b,hb,_,hexact⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt f V
    (chosenProjectiveNormalization_definingIdeal_ne_bot V L hinj hfinite hrn)
    hq hf hV L hL hinj hfinite
    (chosenProjectiveNormalization_chart_dimension V L hinj hfinite x0 hx0) x0 hx0
  have hc : a*b ≠ 0 := mul_ne_zero ha hb
  have hnonempty : ∃ w : Fin ((p+1)+1) → ℂ,MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (MvPolynomial.funext (fun w => by simpa using h w))
  refine ⟨a*b,hc,hnonempty,?_⟩
  intro w hw
  obtain ⟨hwa,hwb⟩ := mul_ne_zero_iff.mp (by simpa only [MvPolynomial.eval_mul] using hw)
  obtain ⟨_,_,_,_,_,he⟩ := hexact w hwb
  exact ⟨(hdual w hwa).1,projectivePulledCutEquation_moduleExt_dual_of_native_dual
    f V L w he (hdual w hwa).2⟩
end LinearStudy
