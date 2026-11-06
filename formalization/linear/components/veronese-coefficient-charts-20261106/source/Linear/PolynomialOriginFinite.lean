module
public import Linear.PolynomialGlobalResidue
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι]

theorem polynomial_origin_radical (I : Ideal (MvPolynomial ι K))
    (hI : MvPolynomial.zeroLocus K I = {0}) :
    I.radical = RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I, hI]
  ext p
  simp [RingHom.mem_ker]

theorem polynomialQuotient_finite_of_origin_zeroLocus (I : Ideal (MvPolynomial ι K))
    (hI : MvPolynomial.zeroLocus K I = {0}) :
    Module.Finite K (MvPolynomial ι K ⧸ I) := by
  let Q := MvPolynomial ι K ⧸ I
  have he : I ≤ RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom := by
    rw [← polynomial_origin_radical I hI]
    exact Ideal.le_radical
  let q : Q →ₐ[K] K := Ideal.Quotient.liftₐ I (MvPolynomial.aeval (R := K) (0 : ι → K)) he
  have hq : Function.Surjective q := fun k => ⟨algebraMap K Q k, q.commutes k⟩
  have hk : RingHom.ker q.toRingHom ≤ nilradical Q := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change MvPolynomial.aeval (R := K) (0 : ι → K) p = 0 at hx
    have hp : p ∈ I.radical := by
      rw [polynomial_origin_radical I hI]
      exact hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
    apply mem_nilradical.mpr
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  exact Module.finite_of_surjective_of_ker_le_nilradical q hq hk
    (IsNoetherian.noetherian (RingHom.ker q.toRingHom))
end LinearStudy
