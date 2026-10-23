module
public import Linear.SchemeModuleGlobalToInternalExtAllDegrees
public import Linear.SchemeModuleCochainIteratedInternalBoundary
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
/-- The ACTUAL all-degree comparison commutes with EVERY SAME original opcycle-source iteration,including the initial Hom class. -/
theorem schemeModuleGlobalToInternalExtAll_iteratedBoundary
    (K : CochainComplex X.Modules ℤ) {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) (e : Ext.{u} (K.opcycles (cochainSourceDegree r 0)) N 0) :
    schemeModuleGlobalToInternalExtAll (K.opcycles (cochainSourceDegree r n)) N n
        (cochainOpcycleIteratedBoundary K r alpha n hn e) =
      schemeModuleGlobalToInternalExtAll (K.opcycles (cochainSourceDegree r 0)) N 0 e ≫
        schemeModuleCochainIteratedInternalBoundary K N r alpha n hn := by
  induction n with
  | zero =>
    rw [schemeModuleCochainIteratedInternalBoundary_zero,Category.comp_id]
    rfl
  | succ n ih =>
    calc
      _ = schemeModuleGlobalToInternalExtAll (K.opcycles (cochainSourceDegree r n)) N n
          (cochainOpcycleIteratedBoundary K r alpha n (by omega) e) ≫
        schemeModuleInternalExtSourceBoundary (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
          (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
            (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega))) N n := by
        rw [cochainOpcycleIteratedBoundary_succ]
        exact schemeModuleGlobalToInternalExtAll_boundary
          (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
          (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
            (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega)))
          N n (cochainOpcycleIteratedBoundary K r alpha n (by omega) e)
      _ = _ := by
        rw [ih (by omega),schemeModuleCochainIteratedInternalBoundary_succ,Category.assoc]
end LinearStudy
