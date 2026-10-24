module
public import Linear.FiniteAdditiveDualRepresentative
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
/-- Retain a NONZERO vector representing a nonzero ORIGINAL scalar-linear
functional,using the already proved finite-dual representation theorem. -/
theorem finiteAdditiveDual_exists_nonzero_representative
    {K H V : Type*} [Field K] [AddCommGroup H] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (e : H ≃+ Module.Dual K V) (rho : K → H → H)
    (hscalar : ∀ r x,e (rho r x)=r • e x)
    (ell : H →+ K) (hlin : ∀ r x,ell (rho r x)=r * ell x) (hell : ell ≠ 0) :
    ∃ v : V,v ≠ 0 ∧ ∀ x,e x v=ell x := by
  obtain ⟨v,hv⟩ := finiteAdditiveDual_exists_representative e rho hscalar ell hlin
  refine ⟨v,?_,hv⟩
  intro hz
  apply hell
  apply AddMonoidHom.ext
  intro x
  have h := (hv x).symm
  rw [hz,map_zero] at h
  exact h
end LinearStudy
