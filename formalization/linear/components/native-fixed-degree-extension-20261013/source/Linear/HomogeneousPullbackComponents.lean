module
public import Linear.AffineFiltered
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K ι κ : Type*} [Field K]

/-- Under substitution by homogeneous forms of positive common degree q,
the q*m homogeneous component is exactly the pullback of component m. -/
theorem homogeneousComponent_aeval_common_positive_degree
    (P : κ → MvPolynomial ι K) (q : ℕ) (hq : 0 < q)
    (hP : ∀ i, (P i).IsHomogeneous q)
    (H : MvPolynomial κ K) (m : ℕ) :
    MvPolynomial.homogeneousComponent (q * m) (MvPolynomial.aeval P H) =
      MvPolynomial.aeval P (MvPolynomial.homogeneousComponent m H) := by
  classical
  have he := congrArg (fun F => MvPolynomial.homogeneousComponent (q * m)
    (MvPolynomial.aeval P F)) (MvPolynomial.sum_homogeneousComponent H)
  simp only [map_sum] at he
  rw [← he]
  rw [Finset.sum_eq_single m]
  · exact MvPolynomial.homogeneousComponent_eq_self
      ((MvPolynomial.homogeneousComponent_isHomogeneous m H).aeval P hP)
  · intro k hk hkm
    have hne : q * m ≠ q * k := fun h => hkm ((mul_left_cancel₀ (ne_of_gt hq) h).symm)
    rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.homogeneousComponent_isHomogeneous k H).aeval P hP)]
    simp [hne]
  · intro hm
    have hlt : H.totalDegree < m := by
      simp only [Finset.mem_range] at hm
      omega
    rw [MvPolynomial.homogeneousComponent_eq_zero m H hlt, map_zero, map_zero]

end LinearStudy
