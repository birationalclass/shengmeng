module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic

/-!
# Difference coefficients with actual diagonal derivatives

For two polynomial maps agreeing on constants and equal after a third map,
construct coefficients of their difference. The third map sends each
coefficient to the corresponding actual partial derivative. This gives
the polynomial part of the diagonal Jacobian construction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {R A B ι : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Fintype ι] [DecidableEq ι]

theorem polynomial_diagonal_difference
    (u v : MvPolynomial ι R →+* A) (π : A →+* B)
    (hC : ∀ c, u (MvPolynomial.C c) = v (MvPolynomial.C c))
    (hX : ∀ i, π (u (MvPolynomial.X i)) = π (v (MvPolynomial.X i)))
    (p : MvPolynomial ι R) :
    ∃ a : ι → A,
      u p - v p = ∑ i, a i * (u (MvPolynomial.X i) - v (MvPolynomial.X i)) ∧
      ∀ i, π (a i) = π (u (MvPolynomial.pderiv i p)) := by
  have hdiag : ∀ p : MvPolynomial ι R, π (u p) = π (v p) := by
    have h := MvPolynomial.ringHom_ext (f := π.comp u) (g := π.comp v)
      (fun c => congrArg π (hC c)) hX
    exact fun p => RingHom.congr_fun h p
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · simp [hC]
    · intro i; simp
  | add p q hp hq =>
    obtain ⟨a, ha, hda⟩ := hp
    obtain ⟨b, hb, hdb⟩ := hq
    refine ⟨fun i => a i + b i, ?_, ?_⟩
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [← ha, ← hb]; ring
    · intro i
      simp only [map_add, hda, hdb]
  | mul_X p j hp =>
    obtain ⟨a, ha, hda⟩ := hp
    refine ⟨fun i => u p * (if i = j then 1 else 0) + v (MvPolynomial.X j) * a i,
      ?_, ?_⟩
    · simp only [add_mul, Finset.sum_add_distrib]
      have hfirst : (∑ i, u p * (if i = j then 1 else 0) *
          (u (MvPolynomial.X i) - v (MvPolynomial.X i))) =
          u p * (u (MvPolynomial.X j) - v (MvPolynomial.X j)) := by
        simp
      rw [hfirst]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← ha]
      simp only [map_mul]
      ring
    · intro i
      simp only [map_add, map_mul, hda]
      rw [← hX j]
      by_cases hij : i = j
      · subst i
        simp [Derivation.leibniz, MvPolynomial.pderiv_X]
      · simp [hij, Derivation.leibniz, MvPolynomial.pderiv_X]

end LinearStudy
