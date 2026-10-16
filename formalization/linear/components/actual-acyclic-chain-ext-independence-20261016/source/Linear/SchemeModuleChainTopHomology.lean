module
public import Linear.SchemeModuleInternalHomComplex
public import Linear.SchemeModuleInternalExtSourceMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL top cohomology of SAME internal-Hom cochain complex is SAME
original Hom-differential cokernel when actual next source term is zero. -/
def schemeModuleChainTopHomologyCokernelIso (K : ChainComplex X.Modules ℕ) (N : X.Modules)
    (p : ℕ) (hAbove : IsZero (K.X (p+2))) :
    (schemeModuleInternalHomCochainComplex N K).homology (p+1) ≅
      cokernel (schemeModuleHomPrecompose (N := N) (K.d (p+1) p)) := by
  let C := schemeModuleInternalHomCochainComplex N K
  let S := C.sc' p (p+1) (p+2)
  have hg : S.g = 0 := by
    change schemeModuleHomPrecompose (N := N) (K.d (p+2) (p+1)) = 0
    rw [hAbove.eq_of_src (K.d (p+2) (p+1)) 0]
    exact schemeModuleHomPrecompose_zero _ _ N
  exact C.homologyIsoSc' p (p+1) (p+2) (by simp) (by simp) ≪≫
    (ShortComplex.HomologyData.ofHasCokernel S hg).left.homologyIso

end LinearStudy
