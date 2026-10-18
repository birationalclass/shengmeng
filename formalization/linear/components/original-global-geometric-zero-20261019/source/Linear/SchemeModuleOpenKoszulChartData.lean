module
public import Linear.SchemeModuleOriginalOpenKoszulQCCutStatement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Actual open chart, equations and chain comparison data ONLY. The desired Ext comparison or class formula is not a field. -/
def schemeModuleOpenKoszulChartData {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (r : ℕ) : Type _ :=
  Σ R : CommRingCat.{u}, Σ j : Spec R ⟶ X, Σ' hj : IsOpenImmersion j,
    Σ H : Fin r → R,
      letI := hj
      letI := schemeModuleOpenRestriction_additive j
      ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
        tildeFunctionKoszulComplex R H
variable {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
variable (D : schemeModuleOpenKoszulChartData C (p+1))
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- The SAME all-quasicoherent-coefficient class formula in actual chart data. This is a Prop definition, not a proof. -/
def schemeModuleOpenKoszulChartDataCutStatement : Prop :=
  letI := D.2.2.1
  schemeModuleOriginalOpenKoszulQCCutStatement D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2
    alpha hAlpha hAbove
/-- Derive the desired class formula from the actual chart and source internal-Ext vanishings. No class-image conclusion is supplied as data. -/
theorem schemeModuleOpenKoszulChartDataCutStatement_proof
    (hA : ∀ (N : X.Modules) (hN : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1))) :
    schemeModuleOpenKoszulChartDataCutStatement C p D alpha hAlpha hAbove := by
  letI := D.2.2.1
  exact schemeModuleOriginalOpenKoszulQCCutStatement_proof D.1 D.2.1 p D.2.2.2.1 C D.2.2.2.2
    alpha hAlpha hAbove hA
end LinearStudy
