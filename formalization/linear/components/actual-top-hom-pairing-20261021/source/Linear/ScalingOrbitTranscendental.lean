module
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Polynomial.Roots
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy

/-- Infinitely many actual scaling images over a fixed intermediate field
force transcendence. The orbit is constructed, not a transcendence axiom. -/
theorem transcendental_of_scaling_orbit
    {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F]
    (E : IntermediateField k F) (t : F) (ht : t ≠ 0)
    (Φ : ℕ → F →ₐ[k] F)
    (hfix : ∀ N, ∀ a ∈ E, Φ N a = a)
    (hscale : ∀ N, Φ N t = algebraMap k F ((N + 1 : ℕ) : k) * t) :
    Transcendental E t := by
  intro halg
  obtain ⟨P, hP, hPt⟩ := halg
  let Q : Polynomial F := P.map E.val.toRingHom
  have hQ : Q ≠ 0 := by
    exact Polynomial.map_ne_zero hP
  have hroots : Set.range (fun N => Φ N t) ⊆ {x | Q.IsRoot x} := by
    rintro _ ⟨N, rfl⟩
    let ψ : F →ₐ[E] F :=
      { (Φ N).toRingHom with commutes' := fun a => hfix N a a.property }
    have he : Polynomial.aeval (Φ N t) P = 0 := by
      change Polynomial.aeval (ψ t) P = 0
      rw [Polynomial.aeval_algHom ψ t, AlgHom.comp_apply, hPt, map_zero]
    change Q.eval (Φ N t) = 0
    rw [Polynomial.eval_map]
    exact he
  have hi : Function.Injective (fun N => Φ N t) := by
    intro N M hNM
    have heq : algebraMap k F ((N + 1 : ℕ) : k) = algebraMap k F ((M + 1 : ℕ) : k) := by
      apply mul_right_cancel₀ ht
      rw [← hscale N, ← hscale M]
      exact hNM
    have hk : ((N + 1 : ℕ) : k) = ((M + 1 : ℕ) : k) :=
      (algebraMap k F).injective heq
    have hnat : N + 1 = M + 1 := by exact_mod_cast hk
    omega
  exact (Set.infinite_range_of_injective hi) ((Polynomial.finite_setOfPred_isRoot hQ).subset hroots)

end LinearStudy
