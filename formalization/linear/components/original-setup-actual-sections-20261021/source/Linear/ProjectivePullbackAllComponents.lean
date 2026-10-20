module
public import Linear.ProjectiveGradedPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K ι κ : Type*} [Field K]

/-- All components of substitution by homogeneous degree-q forms are
computed, including degrees that are not divisible by q. -/
theorem homogeneousComponent_aeval_positive_degree_all
    (P : κ → MvPolynomial ι K) (q : ℕ) (hq : 0 < q)
    (hP : ∀ i, (P i).IsHomogeneous q)
    (H : MvPolynomial κ K) (k : ℕ) :
    MvPolynomial.homogeneousComponent k (MvPolynomial.aeval P H) =
      if q ∣ k then MvPolynomial.aeval P (MvPolynomial.homogeneousComponent (k / q) H)
        else 0 := by
  classical
  by_cases hqk : q ∣ k
  · rw [ite_eq_left hqk]
    obtain ⟨m, rfl⟩ := hqk
    rw [Nat.mul_div_cancel_left m hq]
    exact homogeneousComponent_aeval_common_positive_degree P q hq hP H m
  · rw [ite_eq_right hqk]
    have he := congrArg (fun G => MvPolynomial.homogeneousComponent k
      (MvPolynomial.aeval P G)) (MvPolynomial.sum_homogeneousComponent H)
    rw [← he]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.homogeneousComponent_isHomogeneous m H).aeval P hP)]
    have hkm : k ≠ q * m := fun h => hqk ⟨m, h⟩
    simp [hkm]

variable {n : ℕ}

/-- Exact component formula for the ORIGINAL coordinate pullback in every
degree. This uses the actual original homogeneous tuple and ideal. -/
theorem projectiveCoordinateDomainMap_component_all
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (k : ℕ) (a : CoordinateRing n ⧸ V.ideal.toIdeal) :
    homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous k
        (projectiveCoordinateDomainMap f V hq hf hV a) =
      if f.degree ∣ k then projectiveCoordinateDomainMap f V hq hf hV
        (homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous (k / f.degree) a)
      else 0 := by
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [projectiveCoordinateDomainMap_mk, homogeneousQuotientComponent_mk,
    homogeneousComponent_aeval_positive_degree_all f.forms f.degree hq f.homogeneous,
    apply_ite, map_zero]
  split_ifs <;> rfl

end LinearStudy
