module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.MvPolynomial
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u
set_option backward.isDefEq.respectTransparency false

/-- The kernel of the coordinate restriction to an actual affine line
through a specified rational point is strictly below that point's ideal. -/
theorem affine_line_kernel_below_point
    (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) (a : Fin n → k) :
    ∃ p : Ideal (MvPolynomial (Fin n) k), p.IsPrime ∧
      p < MvPolynomial.vanishingIdeal k {a} ∧
      Nonempty ((MvPolynomial (Fin n) k ⧸ p) ≃+* Polynomial k) := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let v : Fin n → Polynomial k :=
    fun j => if j = i then Polynomial.X else Polynomial.C (a j)
  let β : MvPolynomial (Fin n) k →ₐ[k] Polynomial k := MvPolynomial.aeval v
  let γ : Polynomial k →ₐ[k] MvPolynomial (Fin n) k :=
    Polynomial.aeval (MvPolynomial.X i)
  have hβγ : β.comp γ = AlgHom.id k (Polynomial k) := by
    ext
    simp [β, γ, v]
  have hsurj : Function.Surjective β := by
    intro z
    refine ⟨γ z, ?_⟩
    exact DFunLike.congr_fun hβγ z
  let p := RingHom.ker β.toRingHom
  have hp : p.IsPrime := RingHom.ker_isPrime β.toRingHom
  have heval : (Polynomial.aeval (a i)).comp β = MvPolynomial.aeval a := by
    ext j
    by_cases hj : j = i <;> simp [β, v, hj]
  have hpq : p ≤ MvPolynomial.vanishingIdeal k {a} := by
    intro z hz
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    rw [← heval]
    change (Polynomial.aeval (a i)) (β z) = 0
    rw [show β z = 0 from hz, map_zero]
  have hstrict : p < MvPolynomial.vanishingIdeal k {a} := by
    apply lt_of_le_of_ne hpq
    intro heq
    let w := MvPolynomial.X i - MvPolynomial.C (a i)
    have hw : w ∈ MvPolynomial.vanishingIdeal k {a} := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp [w]
    have hw0 : β w = 0 := by
      have hwp : w ∈ p := heq.symm ▸ hw
      exact hwp
    have hcoeff := congrArg (fun z : Polynomial k => z.coeff 1) hw0
    simp [β, v, w] at hcoeff
  exact ⟨p, hp, hstrict,
    ⟨RingHom.quotientKerEquivOfSurjective hsurj⟩⟩

end Negativity
