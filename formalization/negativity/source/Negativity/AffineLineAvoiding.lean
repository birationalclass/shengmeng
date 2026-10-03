module

public import Negativity.AffineLineThroughPoint
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: a line through the prescribed zero of a nonzero
polynomial can be constructed so that it is not contained in that
polynomial's zero set. This provides genuine support avoidance, not
merely existence of some curve through the point. -/
theorem affine_line_through_point_avoiding_polynomial
    (k : Type u) [Field k] [Infinite k] (n : ℕ) (a : Fin n → k)
    (b : MvPolynomial (Fin n) k) (hb : b ≠ 0) (hba : MvPolynomial.eval a b = 0) :
    ∃ p : Ideal (MvPolynomial (Fin n) k), p.IsPrime ∧
      p < MvPolynomial.vanishingIdeal k {a} ∧ b ∉ p ∧
      Nonempty ((MvPolynomial (Fin n) k ⧸ p) ≃+* Polynomial k) := by
  classical
  have hex : ∃ z : Fin n → k, MvPolynomial.eval z b ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (MvPolynomial.funext (by simpa using h))
  obtain ⟨z, hz⟩ := hex
  have hza : z ≠ a := by
    intro h
    subst z
    exact hz hba
  have hi : ∃ i : Fin n, z i ≠ a i := by
    by_contra h
    push Not at h
    exact hza (funext h)
  obtain ⟨i, hi⟩ := hi
  let δ := z i - a i
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hi
  let v : Fin n → Polynomial k :=
    fun j => Polynomial.C (a j) + Polynomial.C (z j - a j) * Polynomial.X
  let β : MvPolynomial (Fin n) k →ₐ[k] Polynomial k := MvPolynomial.aeval v
  let γ : Polynomial k →ₐ[k] MvPolynomial (Fin n) k :=
    Polynomial.aeval (MvPolynomial.C δ⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)))
  have hβγ : β.comp γ = AlgHom.id k (Polynomial k) := by
    apply Polynomial.algHom_ext
    change β (γ Polynomial.X) = Polynomial.X
    simp only [γ, β]
    simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X,
      AlgHom.coe_id, id_eq, map_mul, map_sub, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X]
    change Polynomial.C δ⁻¹ *
      ((Polynomial.C (a i) + Polynomial.C δ * Polynomial.X) - Polynomial.C (a i)) = _
    rw [add_sub_cancel_left, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hδ]
    simp
  have hsurj : Function.Surjective β := by
    intro w
    exact ⟨γ w, DFunLike.congr_fun hβγ w⟩
  let p := RingHom.ker β.toRingHom
  have hp : p.IsPrime := RingHom.ker_isPrime β.toRingHom
  have heval0 : (Polynomial.aeval (0 : k)).comp β = MvPolynomial.aeval a := by
    ext j
    simp [β, v]
  have heval1 : (Polynomial.aeval (1 : k)).comp β = MvPolynomial.aeval z := by
    ext j
    simp [β, v]
  have hpq : p ≤ MvPolynomial.vanishingIdeal k {a} := by
    intro w hw
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, ← heval0]
    change (Polynomial.aeval (0 : k)) (β w) = 0
    rw [show β w = 0 from hw, map_zero]
  have hstrict : p < MvPolynomial.vanishingIdeal k {a} := by
    apply lt_of_le_of_ne hpq
    intro h
    let w := MvPolynomial.X i - MvPolynomial.C (a i)
    have hw : w ∈ MvPolynomial.vanishingIdeal k {a} := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [w]
    have hwp : w ∈ p := h.symm ▸ hw
    have he := congrArg (fun q : Polynomial k => q.coeff 1) (show β w = 0 from hwp)
    simp [β, v, w] at he
    exact hi (sub_eq_zero.mp he)
  have hbp : b ∉ p := by
    intro h
    apply hz
    have hb0 : β b = 0 := h
    have hv : MvPolynomial.aeval z b = 0 := by
      rw [← heval1]
      change (Polynomial.aeval (1 : k)) (β b) = 0
      rw [hb0, map_zero]
    simpa using hv
  exact ⟨p, hp, hstrict, hbp, ⟨RingHom.quotientKerEquivOfSurjective hsurj⟩⟩

end
end Negativity
