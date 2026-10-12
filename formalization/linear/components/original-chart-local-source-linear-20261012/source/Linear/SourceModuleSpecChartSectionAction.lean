module
public import Linear.SchemeModuleSpecChartSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 180000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (S : TopCat.Sheaf RingCat Y) (α : Y.ringCatSheaf ⟶ S)
variable (M : SheafOfModules.{u} S) (j : Spec R ⟶ Y) [IsOpenImmersion j]

/-- Original Spec-chart section transport preserves the ACTUAL source
scalar action, using the SAME source-ring restriction along the chart.
No scalar relation is supplied as an assumption. -/
theorem sourceModuleSpecChartSectionsEquiv_smul
    (U : Y.Opens) (hi : j ''ᵁ ⊤ = U) (b : S.obj.obj (op U))
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),U)) :
    let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
    schemeModuleSpecChartSectionsEquiv A j U hi (b • (show M.val.obj (op U) from x)) =
      S.obj.map (eqToIso hi).op.hom b •
        (show M.val.obj (op (j ''ᵁ ⊤)) from schemeModuleSpecChartSectionsEquiv A j U hi x) := by
  dsimp only
  change M.val.presheaf.map (eqToIso hi).op.hom
      (b • (show M.val.obj (op U) from x)) =
    S.obj.map (eqToIso hi).op.hom b • M.val.presheaf.map (eqToIso hi).op.hom x
  exact M.val.map_smul (eqToIso hi).op.hom b x
end LinearStudy
