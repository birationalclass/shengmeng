module
public import Linear.SchemeModuleInjectiveInternalHomNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
/-- Every actual unit-valued cycle of the SAME internal-Hom complex is the currying of an original injective cocycle. -/
theorem schemeModuleInjectiveInternalHomCycleMap_surjective {X : Scheme.{u}}
    {N : X.Modules} (I : InjectiveResolution N) (P : X.Modules) (q : ℕ) :
    Function.Surjective (schemeModuleInjectiveInternalHomCycleMap I P q) := by
  intro z
  let K := schemeModuleInjectiveInternalHomComplex I P
  let e := schemeModuleHomUnitAddEquiv P (I.cocomplex.X q)
  let f : P ⟶ I.cocomplex.X q := e (z ≫ K.iCycles q)
  have hf : f ≫ I.cocomplex.d q (q+1) = 0 := by
    apply (schemeModuleHomUnitAddEquiv P (I.cocomplex.X (q+1))).symm.injective
    rw [schemeModuleHomUnitAddEquiv_symm_postcompose, map_zero]
    change e.symm (e (z ≫ K.iCycles q)) ≫ K.d q (q+1) = 0
    rw [e.symm_apply_apply, Category.assoc, K.iCycles_d, comp_zero]
  refine ⟨⟨f,hf⟩, ?_⟩
  apply (cancel_mono (K.iCycles q)).mp
  rw [schemeModuleInjectiveInternalHomCycleMap_i]
  exact e.symm_apply_apply _
end LinearStudy
