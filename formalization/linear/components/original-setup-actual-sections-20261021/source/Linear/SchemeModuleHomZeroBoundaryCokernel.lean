module
public import Linear.SchemeModuleHomToInternalExtZero
public import Linear.SchemeModuleHomSourceBoundaryCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- The ACTUAL initial Hom boundary,under the proved Hom-cokernel comparison,is EXACT the SAME actual Hom quotient class. -/
theorem schemeModuleHomZeroBoundary_cokernel
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (hB : IsZero (schemeModuleInternalExt S.X₂ N 1))
    (a : S.X₁ ⟶ N) :
    schemeModuleHomToInternalExtZero S.X₁ N a ≫
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I 0 ≫
      (schemeModuleHomSourceBoundaryCokernelIso S hS N I hB).inv =
      (schemeModuleHomUnitAddEquiv S.X₁ N).symm a ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) S.f) := by
  let e := schemeModuleHomSourceBoundaryCokernelIso S hS N I hB
  have he := schemeModuleHomSourceBoundaryCokernelIso_hom S hS N I hB
  change ((schemeModuleHomUnitAddEquiv S.X₁ N).symm a ≫
      ((schemeModuleInternalExtZeroIso S.X₁).app N).inv) ≫
      schemeModuleInternalExtSourceBoundaryViaResolution S hS N I 0 ≫ e.inv = _
  calc
    _ = (schemeModuleHomUnitAddEquiv S.X₁ N).symm a ≫
        (cokernel.π (schemeModuleHomPrecompose (N := N) S.f) ≫ e.hom) ≫ e.inv := by
      rw [he]
      simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
end LinearStudy
