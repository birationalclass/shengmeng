module
public import Linear.OriginRegular
public import Linear.ProjectiveChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open RingTheory.Sequence

/-- Nontriviality of all successive quotients rules out a zero member.
This uses the existing regular-sequence API, rather than assuming that the
individual leading forms are nonzero. -/
theorem regular_sequence_mem_ne_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {rs : List R} (h : IsRegular M rs) :
    ∀ x ∈ rs, x ≠ 0 := by
  induction rs generalizing M with
  | nil => simp
  | cons a rs ih =>
    have ht := (isRegular_cons_iff M a rs).mp h
    letI : Nontrivial M := h.nontrivial
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      intro ha
      subst a
      exact IsSMulRegular.not_zero ht.1
    · exact ih ht.2 x hx

/-- For n homogeneous equations in n affine variables, no zero at infinity
proves BOTH the exact common degree and regularity of the actual leading
forms. No nonzero-leading-form assumption is supplied. -/
theorem homogeneous_affine_exact_degree_and_highest_regular
    {K : Type*} [Field K] [IsAlgClosed K] {n q : ℕ}
    (F : Fin n → MvPolynomial (Fin (n + 1)) K) (hq : 0 < q)
    (hF : ∀ i, (F i).IsHomogeneous q)
    (hno : ∀ z : Fin n → K, z ≠ 0 →
      ∃ i, MvPolynomial.eval (Fin.cases 0 z) (F i) ≠ 0) :
    (∀ i, (affineDehomogenize (F i)).totalDegree = q) ∧
      IsRegular (MvPolynomial (Fin n) K)
        (List.ofFn (fun i => MvPolynomial.homogeneousComponent
          (affineDehomogenize (F i)).totalDegree (affineDehomogenize (F i)))) ∧
      MvPolynomial.zeroLocus K (Ideal.span (Set.range (fun i =>
        MvPolynomial.homogeneousComponent (affineDehomogenize (F i)).totalDegree
          (affineDehomogenize (F i))))) = {0} := by
  classical
  let H : Fin n → MvPolynomial (Fin n) K := fun i =>
    MvPolynomial.homogeneousComponent q (affineDehomogenize (F i))
  have hZ := affine_highest_zeroLocus_of_no_infinity F hq hF hno
  have hreg : IsRegular (MvPolynomial (Fin n) K) (List.ofFn H) :=
    homogeneous_origin_regular n H (fun i =>
      ⟨q, MvPolynomial.homogeneousComponent_isHomogeneous _ _⟩) hZ
  have hne (i : Fin n) : H i ≠ 0 :=
    regular_sequence_mem_ne_zero hreg (H i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hd (i : Fin n) : (affineDehomogenize (F i)).totalDegree = q := by
    apply homogeneous_affine_chart_degree (F i) (hF i)
    rw [← homogeneous_affine_chart_top_component (F i) (hF i)]
    exact hne i
  refine ⟨hd, ?_, ?_⟩
  · simpa only [hd] using hreg
  · simpa only [hd] using hZ

end LinearStudy
