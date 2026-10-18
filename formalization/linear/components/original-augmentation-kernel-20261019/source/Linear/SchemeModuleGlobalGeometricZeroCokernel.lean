module
public import Linear.SchemeModuleOpenKoszulChartDataGlobalZero
public import Linear.SchemeModuleChartInternalExtSupport
public import Linear.SchemeModuleFiniteSupportLambdaSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Combine canonical source-naturality and actual chart support
GENERICALLY,before specializing to any large original quotient or twist.
Keep the SAME source e,augmentation and canonical global lambda. -/
theorem schemeModuleOpenKoszulChartDataGlobalZeroProof_of_cokernelLambda
    {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (p : ℕ)
    (D : schemeModuleOpenKoszulChartData C (p+1))
    {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
    (e : cokernel (C.d 1 0) ≅ E)
    (hLocal : schemeModuleOpenKoszulChartDataCutZeroStatement C p D alpha hAlpha hAbove)
    (hLambda : ∀ N,Function.Bijective
      (schemeModuleGlobalToInternalExt (cokernel (C.d 1 0)) N p))
    (hSupport : schemeModuleChartInternalExtSupportStatement C (p+1) D E) :
    schemeModuleOpenKoszulChartDataGlobalZeroStatement C p D alpha hAlpha hAbove := by
  apply schemeModuleOpenKoszulChartDataGlobalZeroProof C p D alpha hAlpha hAbove hLocal
  · intro N
    exact (schemeModuleGlobalToInternalExt_bijective_of_sourceIso e.symm N p (hLambda N)).injective
  · intro N
    exact hSupport N (p+1)
end LinearStudy
