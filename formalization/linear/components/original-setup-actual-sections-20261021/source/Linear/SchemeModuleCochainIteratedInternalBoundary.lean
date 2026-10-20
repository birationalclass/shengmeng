module
public import Linear.SchemeModuleCochainInternalBoundaryStep
public import Mathlib.CategoryTheory.Functor.OfSequence
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
/-- Iterate SAME actual derived-SHEAF-Ext source boundaries; source short exactness is DERIVED from SAME actual augmentation. -/
def schemeModuleCochainIteratedInternalBoundary (K : CochainComplex X.Modules ℤ)
    {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n ≤ r) :
    schemeModuleInternalExt (K.opcycles (cochainSourceDegree r 0)) N 0 ⟶
      schemeModuleInternalExt (K.opcycles (cochainSourceDegree r n)) N n :=
  Functor.OfSequence.map (schemeModuleCochainInternalBoundaryStep K N r alpha) 0 n (Nat.zero_le n)
/-- Exact identity for the empty source-boundary iteration. -/
theorem schemeModuleCochainIteratedInternalBoundary_zero (K : CochainComplex X.Modules ℤ)
    {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha] :
    schemeModuleCochainIteratedInternalBoundary K N r alpha 0 (Nat.zero_le r) = 𝟙 _ :=
  Functor.OfSequence.map_id _ 0
/-- SAME next step uses the actual canonical source boundary with no replacement convention. -/
theorem schemeModuleCochainIteratedInternalBoundary_succ (K : CochainComplex X.Modules ℤ)
    {E : X.Modules} (N : X.Modules) (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj E) [QuasiIso alpha]
    (n : ℕ) (hn : n+1 ≤ r) :
    schemeModuleCochainIteratedInternalBoundary K N r alpha (n+1) hn =
      schemeModuleCochainIteratedInternalBoundary K N r alpha n (by omega) ≫
        schemeModuleInternalExtSourceBoundary (cochainOpcycleSourceSequence K (cochainSourceDegree r n))
          (cochainOpcycleSourceSequence_shortExact K (cochainSourceDegree r n)
            (cochainAugmentation_exactAt_negative K alpha _ (by rw [cochainSourceDegree_eq]; omega))) N n := by
  dsimp only [schemeModuleCochainIteratedInternalBoundary]
  rw [Functor.OfSequence.map_comp _ 0 n (n+1) (Nat.zero_le n) (by omega),
    Functor.OfSequence.map_le_succ,schemeModuleCochainInternalBoundaryStep_eq K N r alpha n (by omega)]
end LinearStudy
