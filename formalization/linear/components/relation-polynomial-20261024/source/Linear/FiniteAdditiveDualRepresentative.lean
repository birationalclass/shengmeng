module
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
/-- A finite dual comparison represents every additive functional linear
for the independently specified ORIGINAL scalar operation. Both scalar
laws are explicit;the native application proves the comparison law from
original coefficient multiplication. No scalar action is transported. -/
theorem finiteAdditiveDual_exists_representative
    {K H V : Type*} [Field K] [AddCommGroup H] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (e : H ≃+ Module.Dual K V) (rho : K → H → H)
    (hscalar : ∀ r x,e (rho r x)=r • e x)
    (ell : H →+ K) (hlin : ∀ r x,ell (rho r x)=r * ell x) :
    ∃ v : V,∀ x,e x v=ell x := by
  letI : Module.Free K V := Module.Free.of_divisionRing K V
  letI : Module.IsReflexive K V := Module.IsReflexive.of_finite_of_free K V
  have hinv (r : K) (y : Module.Dual K V) : e.symm (r • y)=rho r (e.symm y) := by
    apply e.injective
    rw [e.apply_symm_apply,hscalar,e.apply_symm_apply]
  let g : Module.Dual K (Module.Dual K V) := {
    toFun := fun y => ell (e.symm y)
    map_add' := fun y z => by rw [map_add,map_add]
    map_smul' := fun r y => by
      change ell (e.symm (r • y))=r * ell (e.symm y)
      rw [hinv,hlin] }
  refine ⟨(Module.evalEquiv K V).symm g,?_⟩
  intro x
  rw [Module.apply_evalEquiv_symm_apply]
  change ell (e.symm (e x))=ell x
  rw [e.symm_apply_apply]
end LinearStudy
