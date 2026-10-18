module
public import Linear.SchemeModuleChartInternalExtSupport
public import Linear.SchemeModuleInternalExtSupportedUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Derive packaged chart support DIRECTLY from the original ambient
cover and actual source zero restrictions. Never compare two concrete
restriction-adjunction units. -/
theorem schemeModuleChartInternalExtSupportStatement_of_originalCover
    {X : Scheme.{u}} (C : ChainComplex X.Modules ℕ) (r : ℕ)
    (D : schemeModuleOpenKoszulChartData C r) (E : X.Modules)
    {ι : Type*} (V : ι → X.Opens)
    (hc : letI := D.2.2.1
      ∀ x : X,x ∈ D.2.1 ''ᵁ ⊤ ∨ ∃ i,x ∈ V i)
    (hE : ∀ i,IsZero (E.restrict (V i).ι)) :
    schemeModuleChartInternalExtSupportStatement C r D E := by
  letI := D.2.2.1
  intro N q
  exact schemeModuleInternalExt_restrictionUnit_isIso_of_originalCover D.2.1 E N q V hc hE
end LinearStudy
