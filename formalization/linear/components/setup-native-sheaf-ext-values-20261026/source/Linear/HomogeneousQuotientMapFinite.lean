module
public import Linear.HomogeneousQuotientRelation
public import Mathlib.RingTheory.RingHom.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Origin-only common cone zero locus makes the ACTUAL polynomial map
into the SAME homogeneous source quotient finite. No global CM/free input. -/
theorem homogeneous_quotient_polynomial_map_finite_of_origin_zeroLocus
    {K ι κ : Type*} [Field K] [IsAlgClosed K] [Finite ι] [Fintype κ]
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (P : κ → MvPolynomial ι K) (q : ℕ) (hq : 0 < q)
    (hP : ∀ i,(P i).IsHomogeneous q)
    (hZ : MvPolynomial.zeroLocus K (I ⊔ Ideal.span (Set.range P))={0}) :
    (((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval P) :
      MvPolynomial κ K →ₐ[K] MvPolynomial ι K ⧸ I).toRingHom).Finite := by
  classical
  let R := MvPolynomial κ K
  let A := MvPolynomial ι K
  let B := A ⧸ I
  let pi := Ideal.Quotient.mk I
  let phi : R →ₐ[K] B := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval P)
  letI : Algebra R B := phi.toRingHom.toAlgebra
  have hphiC : ∀ c : K,phi (MvPolynomial.C c)=pi (MvPolynomial.C c) :=
    fun c => phi.commutes c
  have hphiX : ∀ i : κ,phi (MvPolynomial.X i)=pi (P i) := by
    intro i
    change Ideal.Quotient.mk I ((MvPolynomial.aeval P) (MvPolynomial.X i))=pi (P i)
    rw [MvPolynomial.aeval_X]
  have hmon : ∀ (c : K) (m : ι →₀ ℕ),
      MvPolynomial.C c*MvPolynomial.monomial m (1:K)=MvPolynomial.monomial m c := by
    intro c m
    rw [MvPolynomial.C_mul_monomial,mul_one]
  let J := I ⊔ Ideal.span (Set.range P)
  letI : Module.Finite K (A ⧸ J) := polynomialQuotient_finite_of_origin_zeroLocus J hZ
  obtain ⟨D,hD⟩ := finite_homogeneous_ideal_contains_large_degree J
    (hI.sup (polynomial_equation_ideal_homogeneous P (fun _ => q) hP))
  let T : Set B := (fun m : ι →₀ ℕ => pi (MvPolynomial.monomial m (1:K))) ''
    {m | m.degree ≤ D}
  have hT : T.Finite := (Finsupp.finite_of_degree_le D).image _
  let N : Submodule R B := Submodule.span R T
  have hlow : ∀ p : A,p.totalDegree ≤ D → pi p ∈ N := by
    intro p hp
    rw [p.as_sum,map_sum]
    apply N.sum_mem
    intro m hm
    have hmd : m.degree ≤ D := (MvPolynomial.le_totalDegree hm).trans hp
    have hmN : pi (MvPolynomial.monomial m (1:K)) ∈ N :=
      Submodule.subset_span ⟨m,hmd,rfl⟩
    have hc := N.smul_mem (MvPolynomial.C (p.coeff m) : R) hmN
    change phi (MvPolynomial.C (p.coeff m))*pi (MvPolynomial.monomial m (1:K)) ∈ N at hc
    simpa only [hphiC,← pi.map_mul,hmon] using hc
  have hall : ∀ n : ℕ,∀ p : A,p.totalDegree=n → pi p ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      by_cases hn : n ≤ D
      · exact hlow p (hp.trans_le hn)
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le D) (Nat.lt_of_not_ge hn)
      let H := MvPolynomial.homogeneousComponent n p
      have hH : H.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n p
      have hHJ : H ∈ J := hD n (Nat.lt_of_not_ge hn) H hH
      obtain ⟨a,ha,had⟩ := homogeneous_quotient_bounded_relation I hI P q hP H n hH hHJ
      have haN : ∀ i,pi (a i) ∈ N := by
        intro i
        have hdeg : (a i).totalDegree ≤ n-q := (had i).totalDegree_le
        exact ih (a i).totalDegree (lt_of_le_of_lt hdeg (Nat.sub_lt hn0 hq)) (a i) rfl
      have hHN : pi H ∈ N := by
        rw [← ha,map_sum]
        apply N.sum_mem
        intro i hi
        have hh := N.smul_mem (MvPolynomial.X i : R) (haN i)
        change phi (MvPolynomial.X i)*pi (a i) ∈ N at hh
        simpa only [hphiX,← pi.map_mul,mul_comm] using hh
      have hr : pi (p-H) ∈ N :=
        ih (p-H).totalDegree (totalDegree_strip_top p n hn0 hp.le) (p-H) rfl
      have hh := N.add_mem hr hHN
      have he : pi (p-H)+pi H=pi p :=
        (pi.map_add (p-H) H).symm.trans (congrArg pi (sub_add_cancel p H))
      exact he ▸ hh
  have hN : N=⊤ := Submodule.eq_top_iff'.mpr (fun z => by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hall p.totalDegree p rfl)
  have hfg : (⊤ : Submodule R B).FG := hN ▸ Submodule.fg_span hT
  exact ⟨hfg⟩
end LinearStudy
