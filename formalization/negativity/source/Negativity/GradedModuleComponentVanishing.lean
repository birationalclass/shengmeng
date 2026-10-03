module
public import Negativity.FiniteGradedModuleGeneratorBound
public import Negativity.GradedModuleMapReuse

@[expose] public section
namespace Negativity
open scoped DirectSum
open GradedMonoid
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A component map vanishes if every homogeneous scalar multiple of the
bounded-degree generators has zero image. Closure under arbitrary polynomial
scalars is proved here using the genuine direct-sum graded action. -/
theorem actual_graded_component_vanishing_of_bounded_generators
    {A : ℕ → Type u} {M : ℕ → Type v} [∀ n, AddCommMonoid (A n)]
    [∀ n, AddCommMonoid (M n)] [DirectSum.GSemiring A] [DirectSum.Gmodule A M]
    {P : Type w} [AddCommMonoid P] (c D : ℕ) (T : M D →+ P)
    (hgen : Submodule.span (⨁ n, A n)
      {x : ⨁ n, M n | ∃ d : ℕ, d ≤ c ∧ ∃ m : M d, x = DirectSum.of M d m} = ⊤)
    (hkill : ∀ (i j : ℕ) (a : A i) (m : M j), j ≤ c →
      T ((DirectSum.of M (i + j) (GSMul.smul a m)) D) = 0) :
    ∀ q : M D, T q = 0 := by
  classical
  let p : (⨁ n, M n) →+ P := T.comp (DFinsupp.evalAddMonoidHom D)
  let L : Submodule (⨁ n, A n) (⨁ n, M n) := {
    carrier := {x | ∀ r : ⨁ n, A n, p (r • x) = 0}
    zero_mem' := by intro r; rw [smul_zero, map_zero]
    add_mem' := by
      intro x y hx hy r
      rw [smul_add, map_add, hx r, hy r, add_zero]
    smul_mem' := by
      intro s x hx r
      rw [← mul_smul]
      exact hx (r * s) }
  have hlow : {x : ⨁ n, M n | ∃ d : ℕ, d ≤ c ∧ ∃ m : M d,
      x = DirectSum.of M d m} ⊆ L := by
    rintro x ⟨j, hj, m, rfl⟩ r
    refine DirectSum.induction_on r ?_ (fun i a => ?_) (fun a b ha hb => ?_)
    · rw [zero_smul, map_zero]
    · rw [DirectSum.Gmodule.of_smul_of]
      exact hkill i j a m hj
    · rw [add_smul, map_add, ha, hb, add_zero]
  have htop : (⊤ : Submodule (⨁ n, A n) (⨁ n, M n)) ≤ L := by
    rw [← hgen]
    exact Submodule.span_le.mpr hlow
  intro q
  have hq := htop (show DirectSum.of M D q ∈
    (⊤ : Submodule (⨁ n, A n) (⨁ n, M n)) from trivial) (1 : ⨁ n, A n)
  rw [one_smul] at hq
  change T ((DirectSum.of M D q) D) = 0 at hq
  simpa only [DirectSum.of_eq_same] using hq

#print axioms actual_graded_component_vanishing_of_bounded_generators
end
end Negativity
