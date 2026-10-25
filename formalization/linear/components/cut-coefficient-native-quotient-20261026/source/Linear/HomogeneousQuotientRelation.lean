module
public import Linear.AffineFiltered
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Degree-bounded homogeneous division MODULO the SAME homogeneous
source ideal. The original quotient map and original equations retained. -/
theorem homogeneous_quotient_bounded_relation
    {K ι κ : Type*} [Field K] [Fintype κ]
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (P : κ → MvPolynomial ι K) (q : ℕ) (hP : ∀ i,(P i).IsHomogeneous q)
    (H : MvPolynomial ι K) (n : ℕ) (hH : H.IsHomogeneous n)
    (hmem : H ∈ I ⊔ Ideal.span (Set.range P)) :
    ∃ a : κ → MvPolynomial ι K,
      Ideal.Quotient.mk I (∑ i,a i*P i)=Ideal.Quotient.mk I H ∧
        ∀ i,(a i).IsHomogeneous (n-q) := by
  classical
  obtain ⟨u,hu,v,hv,he⟩ := Submodule.mem_sup.mp hmem
  let U := MvPolynomial.homogeneousComponent n u
  let V := MvPolynomial.homogeneousComponent n v
  have hU : U ∈ I := MvPolynomial.homogeneousComponent_mem_of_mem hI hu n
  have hV : V ∈ Ideal.span (Set.range P) :=
    MvPolynomial.homogeneousComponent_mem_of_mem
      (polynomial_equation_ideal_homogeneous P (fun _ => q) hP) hv n
  have hUV : U+V=H := by
    have hh := congrArg (MvPolynomial.homogeneousComponent n) he
    simpa only [map_add,MvPolynomial.homogeneousComponent_eq_self hH] using hh
  obtain ⟨a,ha,had⟩ := homogeneous_ideal_bounded_representation P (fun _ => q)
    hP V n (MvPolynomial.homogeneousComponent_isHomogeneous n v) hV
  refine ⟨a,?_,fun i => (had i).1⟩
  rw [ha,← hUV,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hU,zero_add]
end LinearStudy
