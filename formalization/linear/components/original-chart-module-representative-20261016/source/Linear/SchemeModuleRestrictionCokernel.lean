module
public import Linear.SchemeModuleOpenRestrictionExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The native original open restriction preserves the ACTUAL cokernel of
an original map,using its proved preservation of homology. No homology
objects of a specific large complex need to be expanded for this map. -/
def schemeModuleOpenRestrictionCokernelIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {M N : Y.Modules} (d : M ⟶ N) :
    (Scheme.Modules.restrictFunctor j).obj (cokernel d) ≅
      cokernel ((Scheme.Modules.restrictFunctor j).map d) := by
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor j) d

/-- This comparison keeps the SAME original cokernel projection. -/
theorem schemeModuleOpenRestrictionCokernelIso_projection {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {M N : Y.Modules} (d : M ⟶ N) :
    (Scheme.Modules.restrictFunctor j).map (cokernel.π d) ≫
      (schemeModuleOpenRestrictionCokernelIso j d).hom =
      cokernel.π ((Scheme.Modules.restrictFunctor j).map d) := by
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact PreservesCokernel.π_iso_hom (Scheme.Modules.restrictFunctor j) d

end LinearStudy