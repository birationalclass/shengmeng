module
public import Linear.AffineFiltered
public import Mathlib.RingTheory.RingHom.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A positive-degree homogeneous tuple with only the origin as common zero
defines an actually finite polynomial ring homomorphism. Finiteness is proved
by degree descent, not assumed as a geometric input. -/
theorem homogeneous_polynomial_map_finite_of_origin_zeroLocus
    {K ι κ : Type*} [Field K] [IsAlgClosed K] [Finite ι] [Fintype κ]
    (P : κ → MvPolynomial ι K) (q : ℕ) (hq : 0 < q)
    (hP : ∀ i, (P i).IsHomogeneous q)
    (hZ : MvPolynomial.zeroLocus K (Ideal.span (Set.range P)) = {0}) :
    ((MvPolynomial.aeval P : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom).Finite := by
  classical
  let R := MvPolynomial κ K
  let A := MvPolynomial ι K
  let φ : R →ₐ[K] A := MvPolynomial.aeval P
  have hφC : ∀ c : K, φ (MvPolynomial.C c) = MvPolynomial.C c :=
    fun c => φ.commutes c
  have hφX : ∀ i : κ, φ (MvPolynomial.X i) = P i :=
    fun i => MvPolynomial.aeval_X P i
  have hmon : ∀ (c : K) (m : ι →₀ ℕ),
      MvPolynomial.C c * MvPolynomial.monomial m (1 : K) =
        MvPolynomial.monomial m c := by
    intro c m
    rw [MvPolynomial.C_mul_monomial, mul_one]
  let : Algebra R A := φ.toRingHom.toAlgebra
  let I := Ideal.span (Set.range P)
  let : Module.Finite K (A ⧸ I) := polynomialQuotient_finite_of_origin_zeroLocus I hZ
  obtain ⟨B, hB⟩ := finite_homogeneous_ideal_contains_large_degree I
    (polynomial_equation_ideal_homogeneous P (fun _ => q) hP)
  let S : Set A := (fun m : ι →₀ ℕ => MvPolynomial.monomial m (1 : K)) ''
    {m | m.degree ≤ B}
  have hS : S.Finite := (Finsupp.finite_of_degree_le B).image _
  let N : Submodule R A := Submodule.span R S
  have hlow : ∀ p : A, p.totalDegree ≤ B → p ∈ N := by
    intro p hp
    rw [p.as_sum]
    apply N.sum_mem
    intro m hm
    have hmd : m.degree ≤ B := (MvPolynomial.le_totalDegree hm).trans hp
    have hmN : MvPolynomial.monomial m (1 : K) ∈ N :=
      Submodule.subset_span ⟨m, hmd, rfl⟩
    have hc := N.smul_mem (MvPolynomial.C (p.coeff m) : R) hmN
    change φ (MvPolynomial.C (p.coeff m)) * MvPolynomial.monomial m (1 : K) ∈ N at hc
    simpa only [hφC, hmon] using hc
  have hall : ∀ n : ℕ, ∀ p : A, p.totalDegree = n → p ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      by_cases hn : n ≤ B
      · exact hlow p (hp.trans_le hn)
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le B) (Nat.lt_of_not_ge hn)
      let H := MvPolynomial.homogeneousComponent n p
      have hH : H.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n p
      have hHI : H ∈ I := hB n (Nat.lt_of_not_ge hn) H hH
      obtain ⟨a, ha, had⟩ := homogeneous_ideal_bounded_representation P (fun _ => q)
        hP H n hH hHI
      have haN : ∀ i, a i ∈ N := by
        intro i
        have hdeg : (a i).totalDegree ≤ n - q := (had i).1.totalDegree_le
        exact ih (a i).totalDegree (lt_of_le_of_lt hdeg (Nat.sub_lt hn0 hq)) (a i) rfl
      have hHN : H ∈ N := by
        rw [← ha]
        apply N.sum_mem
        intro i hi
        have h := N.smul_mem (MvPolynomial.X i : R) (haN i)
        change φ (MvPolynomial.X i) * a i ∈ N at h
        simpa only [hφX, mul_comm] using h
      have hr : p - H ∈ N :=
        ih (p-H).totalDegree (totalDegree_strip_top p n hn0 hp.le) (p-H) rfl
      have hh := N.add_mem hr hHN
      simpa only [sub_add_cancel] using hh
  have hN : N = ⊤ := Submodule.eq_top_iff'.mpr (fun p => hall p.totalDegree p rfl)
  have hfg : (⊤ : Submodule R A).FG := hN ▸ Submodule.fg_span hS
  exact ⟨hfg⟩

end LinearStudy
