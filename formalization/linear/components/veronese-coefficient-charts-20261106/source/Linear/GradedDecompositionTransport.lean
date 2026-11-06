module
public import Linear.GradedModuleProjection
public import Mathlib.Order.SupIndep
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K M N ι : Type*} [DecidableEq ι] [Field K] [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]
variable (𝓝 : ι → Submodule K N) [DirectSum.Decomposition 𝓝]

theorem transportedGrading_independent (e : M ≃ₗ[K] N) :
    iSupIndep (fun i => (𝓝 i).comap e.toLinearMap) := by
  simpa only [Function.comp_def,Submodule.orderIsoMapComap_symm_apply] using
    (iSupIndep_map_orderIso_iff (Submodule.orderIsoMapComap e).symm).mpr
      (DirectSum.Decomposition.isInternal 𝓝).submodule_iSupIndep

theorem transportedGrading_total (e : M ≃ₗ[K] N) :
    (⨆ i, (𝓝 i).comap e.toLinearMap) = ⊤ := by
  let E := (Submodule.orderIsoMapComap e).symm
  have h := E.map_iSup 𝓝
  rw [(DirectSum.Decomposition.isInternal 𝓝).submodule_iSup_eq_top,OrderIso.map_top] at h
  exact h.symm

/-- Transport an actual internal grading through an actual linear
equivalence, preserving the underlying module's original carrier. -/
@[instance_reducible] def transportedGrading (e : M ≃ₗ[K] N) :
    DirectSum.Decomposition (fun i => (𝓝 i).comap e.toLinearMap) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (transportedGrading_independent 𝓝 e)
    (transportedGrading_total 𝓝 e)).chooseDecomposition

end LinearStudy
