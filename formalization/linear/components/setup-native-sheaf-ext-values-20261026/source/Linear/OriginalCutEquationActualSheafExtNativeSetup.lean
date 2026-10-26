module
public import Linear.OriginalCutEquationCoefficientNativeDual
public import Linear.OriginalCutEquationActualSheafExtNativeDuality
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
/-- FULL ORIGINAL Setup DERIVES one nonempty SAME open with actual source
exactness,actual native C_H coefficient values and actual derived SHEAF
Ext/original-class law. No extra comparison or coefficient condition is
added to Setup. Fixed original C_L and SAME geometric top-H remain OPEN. -/
theorem projectivePulledCutEquation_originalSetup_exists_actualSheafExt_native_values_open {n p : ℕ}
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
        projectivePulledCutEquationActualSheafExtNativeStatement f V L w := by
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
  exact ⟨(hdual w hwa).1,projectivePulledCutEquation_actualSheafExt_native_of_duality
    f V L w he (hdual w hwa).2⟩
end LinearStudy
