module
public import Linear.SchemeModuleGlobalExtActualHCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
/-- A SAME bound for positive actual H gives the SAME bound for positive global
unit Ext,for ANY original coefficient family.This uses the proved canonical
Ext/H equivalence and adds no affine,local-free or relative-source premise. -/
theorem schemeModuleActualHBound_globalUnitExtBound (X : Scheme.{u})
    (F : ℤ → X.Modules) (N : ℕ)
    (hH : ∀ k : ℤ,(N : ℤ) ≤ k → ∀ q : ℕ,
      Subsingleton (schemeModuleActualCohomology X (F k) (q+1))) :
    ∀ k : ℤ,(N : ℤ) ≤ k → ∀ i : ℕ,0 < i →
      Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) (F k) i) := by
  intro k hk i hi
  cases i with
  | zero => omega
  | succ q =>
    letI := hH k hk q
    exact (schemeModuleGlobalExtActualHAddEquiv X (F k) (q+1)).injective.subsingleton
end LinearStudy
