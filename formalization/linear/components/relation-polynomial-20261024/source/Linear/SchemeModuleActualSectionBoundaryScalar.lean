module
public import Linear.SchemeModuleScalarExtCentrality
public import Linear.SchemeModuleOriginalActualSectionBoundary
public import Linear.SchemeModuleActualHGlobalSectionsModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
universe u
/-- Evaluation-at-one section identification respects ORIGINAL global
structure-section multiplication,with actual coefficient map on E. -/
theorem schemeModuleUnitHomGlobalSections_symm_originalScalar
    (X : Scheme.{u}) (E : X.Modules) (z : Γ(X,⊤)) (s : Γ(E,⊤)) :
    (schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm (z • s) =
      (schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm s ≫ originalGlobalModuleScalar z E := by
  apply (schemeModuleUnitHomGlobalSectionsAddEquiv X E).injective
  rw [AddEquiv.apply_symm_apply]
  change z • s = (originalGlobalModuleScalar z E).app ⊤
    ((schemeModuleUnitHomGlobalSectionsAddEquiv X E)
      ((schemeModuleUnitHomGlobalSectionsAddEquiv X E).symm s))
  rw [AddEquiv.apply_symm_apply,originalGlobalModuleScalar_app]
  have hi : X.presheaf.map (TopologicalSpace.Opens.leTop (⊤ : X.Opens)).op z=z := by
    change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) z=z
    rw [X.presheaf.map_id]
    rfl
  rw [hi]
/-- The SAME original Ext-class section boundary commutes with ORIGINAL
coefficient multiplication. Derived from global Ext centrality,original
unit-Hom sections and canonical Ext/H naturality,without a desired
boundary-linearity premise. -/
theorem schemeModuleExtClassActualSectionBoundary_originalScalar
    (X : Scheme.{u}) {E M : X.Modules} (r : ℕ) (epsilon : Ext.{u} E M r)
    (z : Γ(X,⊤)) (s : Γ(E,⊤)) :
    schemeModuleExtClassActualSectionBoundary epsilon (z • s) =
      CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf X).map
        (originalGlobalModuleScalar z M)) r
        (schemeModuleExtClassActualSectionBoundary epsilon s) := by
  unfold schemeModuleExtClassActualSectionBoundary
  rw [schemeModuleUnitHomGlobalSections_symm_originalScalar,← Ext.mk₀_comp_mk₀_assoc]
  rw [← schemeModuleGlobalScalar_ext_centrality X z r epsilon]
  rw [← Ext.comp_assoc_of_third_deg_zero]
  exact schemeModuleGlobalExtActualHAddEquiv_naturality X (originalGlobalModuleScalar z M) r _
end LinearStudy
