module
public import Linear.PolynomialOriginFinite
public import Linear.PolynomialDoubleFiber
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Tactic

/-! A graded foundation for low-degree residue vanishing. This module proves the homogeneous, origin-supported complete-intersection case only. General affine Euler-Jacobi and geometric residue comparison are not claimed. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace LinearStudy
variable {K ι : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def homogeneousQuotientComponent (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (n : ℕ) :
    (MvPolynomial ι K ⧸ I) →ₗ[K] (MvPolynomial ι K ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (MvPolynomial.homogeneousComponent n)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact MvPolynomial.homogeneousComponent_mem_of_mem hI hp n)

theorem homogeneousQuotientComponent_mk (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (n : ℕ)
    (p : MvPolynomial ι K) :
    homogeneousQuotientComponent I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent n p) := rfl

theorem homogeneousQuotientComponent_of_low_degree (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (n : ℕ)
    (p : MvPolynomial ι K) (hp : p.totalDegree < n) :
    homogeneousQuotientComponent I hI n (Ideal.Quotient.mk I p) = 0 := by
  rw [homogeneousQuotientComponent_mk, MvPolynomial.homogeneousComponent_eq_zero _ _ hp, map_zero]

theorem homogeneousQuotientComponent_of_homogeneous (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (n : ℕ)
    (p : MvPolynomial ι K) (hp : p.IsHomogeneous n) :
    homogeneousQuotientComponent I hI n (Ideal.Quotient.mk I p) = Ideal.Quotient.mk I p := by
  rw [homogeneousQuotientComponent_mk, MvPolynomial.homogeneousComponent_eq_self hp]

theorem polynomial_equation_ideal_homogeneous {κ : Type*}
    (P : κ → MvPolynomial ι K) (d : κ → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    (Ideal.span (Set.range P)).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K) := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, rfl⟩
  exact ⟨d i, hP i⟩

theorem homogeneous_polynomial_matrix_det [Fintype ι] [DecidableEq ι] {σ : Type*}
    (M : Matrix ι ι (MvPolynomial σ K)) (d : ι → ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous (d i)) :
    M.det.IsHomogeneous (∑ i, d i) := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  have hp : (∏ i, M (e i) i).IsHomogeneous (∑ i, d (e i)) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => hM (e i) i)
  rw [Equiv.sum_comp e d] at hp
  have hs : Equiv.Perm.sign e = 1 ∨ Equiv.Perm.sign e = -1 := Int.units_eq_one_or e.sign
  rcases hs with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

theorem homogeneous_euler_coefficient_matrix [Fintype ι] [DecidableEq ι] [CharZero K]
    (P : ι → MvPolynomial ι K) (d : ι → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    let M : Matrix ι ι (MvPolynomial ι K) :=
      fun i j => MvPolynomial.C ((d i : K)⁻¹) * MvPolynomial.pderiv j (P i)
    M.mulVec MvPolynomial.X = P ∧ M.det.IsHomogeneous (∑ i, (d i - 1)) := by
  dsimp
  constructor
  · funext i
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [mul_assoc, mul_comm (MvPolynomial.pderiv _ _)]
    rw [← Finset.mul_sum, (hP i).sum_X_mul_pderiv]
    have hne : (d i : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (hd i))
    simp only [nsmul_eq_mul, ← mul_assoc]
    rw [show (d i : MvPolynomial ι K) = MvPolynomial.C (d i : K) by simp,
      ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
  · apply homogeneous_polynomial_matrix_det _ _
    intro i j
    exact (hP i).pderiv.C_mul _

def polynomialOriginMap [IsAlgClosed K] [Finite ι]
    (I : Ideal (MvPolynomial ι K)) (hI : MvPolynomial.zeroLocus K I = {0}) :
    (MvPolynomial ι K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (R := K) (0 : ι → K)) (by
    change I ≤ RingHom.ker (MvPolynomial.aeval (R := K) (0 : ι → K)).toRingHom
    rw [← polynomial_origin_radical I hI]
    exact Ideal.le_radical)

theorem polynomialOriginMap_kernel [IsAlgClosed K] [Finite ι]
    (I : Ideal (MvPolynomial ι K)) (hI : MvPolynomial.zeroLocus K I = {0}) :
    RingHom.ker (polynomialOriginMap I hI).toRingHom = nilradical (MvPolynomial ι K ⧸ I) := by
  apply le_antisymm
  · intro x hx
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
  · have hmax := RingHom.ker_isMaximal_of_surjective (polynomialOriginMap I hI).toRingHom
      (fun k => ⟨algebraMap K (MvPolynomial ι K ⧸ I) k, (polynomialOriginMap I hI).commutes k⟩)
    let := hmax.isPrime
    exact nilradical_le_prime _

theorem polynomialOriginMap_maximal [IsAlgClosed K] [Finite ι]
    (I : Ideal (MvPolynomial ι K)) (hI : MvPolynomial.zeroLocus K I = {0})
    (j : MaximalSpectrum (MvPolynomial ι K ⧸ I)) :
    j.asIdeal = RingHom.ker (polynomialOriginMap I hI).toRingHom := by
  have hmax := RingHom.ker_isMaximal_of_surjective (polynomialOriginMap I hI).toRingHom
    (fun k => ⟨algebraMap K (MvPolynomial ι K ⧸ I) k, (polynomialOriginMap I hI).commutes k⟩)
  symm
  apply hmax.eq_of_le j.isMaximal.ne_top
  rw [polynomialOriginMap_kernel]
  let := j.isMaximal.isPrime
  exact nilradical_le_prime _

theorem homogeneous_polynomial_low_degree_pairing [IsAlgClosed K] [CharZero K]
    {n : ℕ} (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (e : Fin (n + 1) → ℕ) (he : ∀ i, 0 < e i)
    (hh : ∀ i, (P i).IsHomogeneous (e i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K) (List.ofFn P))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range P)) = {0}) :
    let Q := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span (Set.range P)
    let pi := Ideal.Quotient.mk (Ideal.span (Set.range P))
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
      fun i j => MvPolynomial.C ((e i : K)⁻¹) * MvPolynomial.pderiv j (P i)
    ∃ p : PerfectMultiplicationPairing (B := K) (A := Q),
      p.functional (pi M.det) = 1 ∧
      (∀ f : MvPolynomial (Fin (n + 1)) K,
        f.totalDegree < ∑ i, (e i - 1) → p.functional (pi f) = 0) ∧
      ∀ j : ℕ, j ≠ ∑ i, (e i - 1) →
        ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous j → p.functional (pi f) = 0 := by
  classical
  let I := Ideal.span (Set.range P)
  let Q := MvPolynomial (Fin (n + 1)) K ⧸ I
  let pi := Ideal.Quotient.mk I
  let q := polynomialOriginMap I hz
  let : Module.Finite K Q := polynomialQuotient_finite_of_origin_zeroLocus I hz
  let : IsNoetherianRing Q := IsNoetherianRing.of_finite K Q
  let : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
    fun i j => MvPolynomial.C ((e i : K)⁻¹) * MvPolynomial.pderiv j (P i)
  obtain ⟨hM, hhom⟩ := homogeneous_euler_coefficient_matrix P e hh he
  change M.mulVec MvPolynomial.X = P at hM
  have hcoord := polynomial_quotient_coordinateIdeal_eq_kernel P q
  change (Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C
    (q (pi (MvPolynomial.X i)))))).map pi = RingHom.ker q.toRingHom at hcoord
  have hqa : ∀ i, q (pi (MvPolynomial.X i)) = 0 := by
    intro i
    change MvPolynomial.aeval (R := K) (0 : Fin (n + 1) → K) (MvPolynomial.X i) = 0
    simp
  simp only [hqa, map_zero, sub_zero] at hcoord
  have hgen : (RingHom.ker q.toRingHom).annihilator = Ideal.span {pi M.det} := by
    rw [← hcoord]
    exact coordinate_annihilator_eq_coefficientDeterminant P MvPolynomial.X hreg
      (polynomial_variables_regular (n + 1)) M hM
  have hne : pi M.det ≠ 0 := by
    have ht := polynomial_coefficientDeterminant_ne_zero_at_point P hreg q M
      (by
        change M.mulVec (fun i => MvPolynomial.X i - MvPolynomial.C
          (q (pi (MvPolynomial.X i)))) = P
        simpa only [hqa, map_zero, sub_zero] using hM)
    exact ht
  obtain ⟨rho, hrho⟩ := Module.Projective.exists_dual_eq_one K hne
  have hI := polynomial_equation_ideal_homogeneous P e hh
  let ell := rho.comp (homogeneousQuotientComponent I hI (∑ i, (e i - 1)))
  have hell : ell (pi M.det) = 1 := by
    change rho (homogeneousQuotientComponent I hI _ (pi M.det)) = 1
    rw [homogeneousQuotientComponent_of_homogeneous I hI _ M.det hhom]
    exact hrho
  have hsoc : ∀ j : MaximalSpectrum Q, ∀ x : Q,
      x ∈ j.asIdeal.annihilator → ∃ b : K, x = b • pi M.det := by
    intro j x hx
    rw [polynomialOriginMap_maximal I hz j] at hx
    exact kernel_socle_scalar_generation q (pi M.det) hgen x hx
  let p := perfectPairingOfGlobalSocles (fun _ : MaximalSpectrum Q => pi M.det)
    hsoc ell (fun _ => by rw [hell]; exact one_ne_zero)
  refine ⟨p, hell, ?_, ?_⟩
  · intro f hf
    change rho (homogeneousQuotientComponent I hI _ (pi f)) = 0
    rw [homogeneousQuotientComponent_of_low_degree I hI _ f hf, map_zero]
  · intro j hj f hf
    change rho (homogeneousQuotientComponent I hI _ (pi f)) = 0
    rw [homogeneousQuotientComponent_mk, MvPolynomial.homogeneousComponent_of_mem hf,
      ite_eq_right (Ne.symm hj), map_zero, map_zero]

theorem homogeneous_perfect_pairing_high_degree_mem
    (I : Ideal (MvPolynomial ι K))
    (p : PerfectMultiplicationPairing (B := K) (A := MvPolynomial ι K ⧸ I)) (D : ℕ)
    (hv : ∀ j : ℕ, j ≠ D → ∀ f : MvPolynomial ι K, f.IsHomogeneous j →
      p.functional (Ideal.Quotient.mk I f) = 0)
    (f : MvPolynomial ι K) (j : ℕ) (hf : f.IsHomogeneous j) (hj : D < j) : f ∈ I := by
  classical
  let pi := Ideal.Quotient.mk I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply p.equiv.injective
  rw [map_zero]
  ext x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [p.equiv_apply]
  change p.functional (pi f * pi g) = 0
  rw [← map_mul]
  have hsum : f * g = ∑ k ∈ Finset.range (g.totalDegree + 1),
      f * MvPolynomial.homogeneousComponent k g := by
    rw [← Finset.mul_sum, MvPolynomial.sum_homogeneousComponent]
  rw [hsum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  exact hv (j + k) (by omega) _ (hf.mul (MvPolynomial.homogeneousComponent_isHomogeneous k g))

theorem homogeneous_polynomial_top_degree_bound [IsAlgClosed K] [CharZero K]
    {n : ℕ} (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (e : Fin (n + 1) → ℕ) (he : ∀ i, 0 < e i)
    (hh : ∀ i, (P i).IsHomogeneous (e i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K) (List.ofFn P))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range P)) = {0}) :
    ∀ j : ℕ, (∑ i, (e i - 1)) < j →
      ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous j →
        f ∈ Ideal.span (Set.range P) := by
  obtain ⟨p, _, _, hv⟩ := homogeneous_polynomial_low_degree_pairing P e he hh hreg hz
  intro j hj f hf
  exact homogeneous_perfect_pairing_high_degree_mem _ p _ hv f j hf hj

end LinearStudy
