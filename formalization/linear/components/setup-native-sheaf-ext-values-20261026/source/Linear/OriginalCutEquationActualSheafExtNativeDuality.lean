module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.OriginalCutEquationActualSheafExtNativeStatement
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
/-- Actual original native B-linear coefficient duality and SAME source
Koszul exactness DERIVE actual derived SHEAF Ext/native-target class law
and coefficient values.No SHEAF Ext iso or desired class square is input. -/
theorem projectivePulledCutEquation_actualSheafExt_native_of_duality {n p : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (w : Fin ((p+1)+1) → ℂ)
    (he : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let H : Fin (p+1) → B := fun i => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
      ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination B H)).ExactAt j)
    (hdual : projectivePulledCutEquationCoefficientNativeDualStatement f V L w) :
    projectivePulledCutEquationActualSheafExtNativeStatement f V L w := by
  unfold projectivePulledCutEquationActualSheafExtNativeStatement
  dsimp only
  apply affineKoszulActualSheafExtNativeDirectValuesStatement_of_coefficient
  · exact he
  · exact hdual
end LinearStudy
