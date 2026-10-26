module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.AffineKoszulActualSheafExtNativeDirectValues
public import Linear.ProjectiveCutAffineKoszul
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
attribute [local irreducible] affineKoszulActualSheafExtNativeDirectValuesStatement
  coextensionOriginalDualEquiv projectivePulledCutEquationMap projectivePulledCutOriginalRingMap
/-- ACTUAL derived SHEAF Ext for SAME original ordered quotient-cut and
actual cut-dependent native coextension C_H. One actual coefficient-sheaf
iso preserves every original polynomial value and literal eval1;the SAME
original roof class/canonical lambda law lands in that SAME native target.
Statement only;fixed original C_L,global twists and SAME top-H are open. -/
def projectivePulledCutEquationActualSheafExtNativeStatement {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ) : Prop :=
    let R := MvPolynomial (Fin (p+1)) ℂ
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let J := (projectivePulledLinearSectionIdeal f V L w).map
      (affineChartPolynomialMap (K:=ℂ)).toRingHom
    let Q := MvPolynomial (Fin n) ℂ ⧸ J
    let phi := projectivePulledCutEquationMap f V L w
    let : Algebra R B := phi.toRingHom.toAlgebra
    let : SMul R B := phi.toRingHom.toAlgebra.toSMul
    let : Module R B := @Algebra.toModule R B _ _ phi.toRingHom.toAlgebra
    let : Algebra R ℂ := (MvPolynomial.aeval (R:=ℂ) (0 : Fin (p+1) → ℂ)).toRingHom.toAlgebra
    let D : ModuleCat B := (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)
    let Dq : ModuleCat Q := (ModuleCat.coextendScalars (algebraMap ℂ Q)).obj (ModuleCat.of ℂ ℂ)
    let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
    let beta : CommRingCat.of B ⟶ CommRingCat.of Q :=
      CommRingCat.ofHom (projectivePulledCutOriginalRingMap f V L w).toRingHom
    affineKoszulActualSheafExtNativeDirectValuesStatement (R:=CommRingCat.of B) (S:=CommRingCat.of Q) beta p H D Dq (MvPolynomial (Fin n) ℂ)
      (fun ell P z => (ModuleCat.CoextendScalars.equiv (algebraMap ℂ Q) (ModuleCat.of ℂ ℂ) (show Dq from z)) (Ideal.Quotient.mk J P)=
        algebraMap R ℂ ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell))
            (Ideal.Quotient.mk V.affineIdeal P)))
      (fun ell z => (ModuleCat.CoextendScalars.equiv (algebraMap ℂ Q) (ModuleCat.of ℂ ℂ) (show Dq from z)) (1:Q)=algebraMap R ℂ
        ((coextensionOriginalDualEquiv (R:=R) (S:=B)
          (show (ModuleCat.restrictScalars (algebraMap R B)).obj D from ell)) 1))
end LinearStudy
