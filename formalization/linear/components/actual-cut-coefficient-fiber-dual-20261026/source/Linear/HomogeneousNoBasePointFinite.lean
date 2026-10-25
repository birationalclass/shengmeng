module
public import Linear.HomogeneousQuotientMapFinite
public import Linear.LinearNormalizationBasePoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Actual positive-degree cone map is finite from NO BASE POINT on the
SAME homogeneous source. A point of that source derives its origin point.
This does not identify a new coefficient dual with the fixed original one. -/
theorem homogeneous_quotient_map_finite_of_no_base_points
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {κ : Type*} [Fintype κ]
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (v : Fin n → K) (hv : v ∈ MvPolynomial.zeroLocus K I)
    (P : κ → MvPolynomial (Fin n) K) (q : ℕ) (hq : 0 < q)
    (hP : ∀ i,(P i).IsHomogeneous q)
    (hno : ∀ z : Fin n → K,z ≠ 0 → z ∈ MvPolynomial.zeroLocus K I →
      ∃ i,MvPolynomial.eval z (P i) ≠ 0) :
    (((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval P) :
      MvPolynomial κ K →ₐ[K] MvPolynomial (Fin n) K ⧸ I).toRingHom).Finite := by
  have hzeroI : (0 : Fin n → K) ∈ MvPolynomial.zeroLocus K I := by
    simpa only [zero_smul] using homogeneous_zeroLocus_smul I hI v hv (0:K)
  have hzeroP (i : κ) : MvPolynomial.eval (0 : Fin n → K) (P i)=0 := by
    simpa only [zero_smul,zero_pow (Nat.ne_of_gt hq),zero_mul] using
      homogeneous_eval_smul (hP i) (0:K) (0 : Fin n → K)
  have hZ : MvPolynomial.zeroLocus K (I ⊔ Ideal.span (Set.range P))={0} := by
    apply Set.Subset.antisymm
    · intro z hz
      apply Set.mem_singleton_iff.mpr
      by_contra hn
      obtain ⟨i,hi⟩ := hno z hn
        (MvPolynomial.zeroLocus_anti_mono le_sup_left hz)
      apply hi
      simpa only [MvPolynomial.aeval_eq_eval] using
        hz (P i) (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i)))
    · intro z hz
      have he : z=0 := Set.mem_singleton_iff.mp hz
      subst z
      have hker : I ⊔ Ideal.span (Set.range P) ≤
          RingHom.ker (MvPolynomial.aeval (R:=K) (0 : Fin n → K)).toRingHom := by
        apply sup_le
        · exact hzeroI
        · apply Ideal.span_le.mpr
          rintro _ ⟨i,rfl⟩
          change MvPolynomial.aeval (R:=K) (0 : Fin n → K) (P i)=0
          simpa only [MvPolynomial.aeval_eq_eval] using hzeroP i
      exact hker
  exact homogeneous_quotient_polynomial_map_finite_of_origin_zeroLocus I hI P q hq hP hZ
end LinearStudy
