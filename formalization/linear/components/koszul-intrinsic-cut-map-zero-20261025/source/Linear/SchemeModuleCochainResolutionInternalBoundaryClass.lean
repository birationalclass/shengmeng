module
public import Linear.SchemeModuleGlobalToInternalExtIteration
public import Linear.CochainResolutionIteratedSourceBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- The ACTUAL comparison of SAME original roof class equals SAME actual internal boundary iteration of the original top functional,after canonical source quotient identification. -/
theorem schemeModuleCochainResolutionTopExtClass_internalBoundary
    (K : CochainComplex X.Modules ℤ) [K.IsStrictlyLE 0] {E N : X.Modules}
    (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (a : K.X (-(r : ℤ)) ⟶ N) (ha : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ a = 0) :
    letI := HasDerivedCategory.standard X.Modules
    schemeModuleGlobalToInternalExtAll (K.opcycles (cochainSourceDegree r r)) N r
      ((Ext.mk₀ (cochainSourceTerminalMap r (cochainAugmentationOpcycle alpha))).comp
        (cochainResolutionTopExtClass K r alpha a ha) (zero_add r)) =
      schemeModuleHomToInternalExtZero (K.opcycles (cochainSourceDegree r 0)) N
        (cochainTopOpcycleFunctional K r a ha) ≫
          schemeModuleCochainIteratedInternalBoundary K N r alpha r le_rfl := by
  letI := HasDerivedCategory.standard X.Modules
  have h := schemeModuleGlobalToInternalExtAll_iteratedBoundary K N r alpha r le_rfl
    (Ext.mk₀ (cochainTopOpcycleFunctional K r a ha))
  rw [cochainResolutionTopExtClass_iteratedSourceBoundary K r hr alpha a ha (injectiveResolution N),
    schemeModuleGlobalToInternalExtAll_mkZero] at h
  exact h
end LinearStudy
