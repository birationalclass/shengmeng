module
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- A nonzero finite-type algebra over an algebraically closed field has
an actual rational point, constructed using a maximal ideal and Zariski's lemma. -/
theorem finiteType_exists_rational_point
    {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.FiniteType K A] : Nonempty (A →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  letI : M.IsMaximal := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  letI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let φ : (A ⧸ M) →ₐ[K] K := IsAlgClosed.lift
  exact ⟨φ.comp (Ideal.Quotient.mkₐ K M)⟩

end LinearStudy
