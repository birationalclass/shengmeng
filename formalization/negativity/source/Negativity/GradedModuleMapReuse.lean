module
public import Negativity.GradedModuleQuotientReuse
public import Mathlib.Data.Sigma.Basic

@[expose] public section
namespace Negativity
open GradedMonoid
open scoped DirectSum
universe u v w
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[instance_reducible]
def actualGradedModuleOfInjective
    {A : ℕ → Type u} {M : ℕ → Type v} {N : ℕ → Type w}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (M n)]
    [∀ n, AddCommMonoid (N n)] [GMonoid A] [DirectSum.Gmodule A M]
    [GSMul A N]
    (q : ∀ n, N n →+ M n) (hq : ∀ n, Function.Injective (q n))
    (hsmul : ∀ (i j : ℕ) (a : A i) (m : N j),
      q (i + j) (GSMul.smul a m) = GSMul.smul a (q j m)) :
    DirectSum.Gmodule A N := by
  let qs : GradedMonoid N → GradedMonoid M := Sigma.map id (fun n => q n)
  have hqs (a : GradedMonoid A) (b : GradedMonoid N) :
      qs (a • b) = a • qs b := by
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    exact congrArg (Sigma.mk (i + j)) (hsmul i j a b)
  have hqsinj : Function.Injective qs := Function.injective_id.sigma_map hq
  refine {
    smul := GSMul.smul
    one_smul := ?_
    mul_smul := ?_
    smul_add := ?_
    smul_zero := ?_
    add_smul := ?_
    zero_smul := ?_ }
  · intro b
    apply hqsinj
    rw [hqs, GMulAction.one_smul]
  · intro a a' b
    apply hqsinj
    rw [hqs, hqs, hqs, GMulAction.mul_smul]
  · intro i j a b c
    apply hq (i + j)
    rw [hsmul, map_add, DirectSum.GdistribMulAction.smul_add, map_add, hsmul, hsmul]
  · intro i j a
    apply hq (i + j)
    rw [hsmul, map_zero, DirectSum.GdistribMulAction.smul_zero, map_zero]
  · intro i j a a' b
    apply hq (i + j)
    rw [hsmul, map_add, hsmul, hsmul, DirectSum.Gmodule.add_smul]
  · intro i j b
    apply hq (i + j)
    rw [hsmul, map_zero, DirectSum.Gmodule.zero_smul]

/-- A proved degree-preserving compatible map is linear for the complete
direct-sum scalar ring, not merely for degree-zero scalars. -/
def actualGradedModuleMap
    {A : ℕ → Type u} {M : ℕ → Type v} {N : ℕ → Type w}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (M n)]
    [∀ n, AddCommMonoid (N n)] [DirectSum.GSemiring A]
    [DirectSum.Gmodule A M] [DirectSum.Gmodule A N]
    (q : ∀ n, M n →+ N n)
    (hsmul : ∀ (i j : ℕ) (a : A i) (m : M j),
      q (i + j) (GSMul.smul a m) = GSMul.smul a (q j m)) :
    (⨁ n, M n) →ₗ[⨁ n, A n] (⨁ n, N n) :=
  { DirectSum.map q with
    map_smul' := by
      intro r x
      change (DirectSum.map q) (r • x) = r • (DirectSum.map q) x
      refine DirectSum.induction_on r ?_ (fun i a => ?_) (fun r s hr hs => ?_)
      · simp only [zero_smul, map_zero]
      · refine DirectSum.induction_on x ?_ (fun j m => ?_) (fun x y hx hy => ?_)
        · simp only [smul_zero, map_zero]
        · simp only [DirectSum.Gmodule.of_smul_of, DirectSum.map_of, vadd_eq_add, hsmul]
        · rw [smul_add, map_add, map_add, smul_add, hx, hy]
      · rw [add_smul, map_add, add_smul, hr, hs] }

theorem actualGradedModuleMap_injective
    {A : ℕ → Type u} {M : ℕ → Type v} {N : ℕ → Type w}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (M n)]
    [∀ n, AddCommMonoid (N n)] [DirectSum.GSemiring A]
    [DirectSum.Gmodule A M] [DirectSum.Gmodule A N]
    (q : ∀ n, M n →+ N n)
    (hsmul : ∀ (i j : ℕ) (a : A i) (m : M j),
      q (i + j) (GSMul.smul a m) = GSMul.smul a (q j m))
    (hq : ∀ n, Function.Injective (q n)) :
    Function.Injective (actualGradedModuleMap q hsmul) := by
  intro a b hab
  ext n
  apply hq n
  exact congrArg (fun x => x n) hab

#print axioms actualGradedModuleOfInjective
#print axioms actualGradedModuleMap
#print axioms actualGradedModuleMap_injective
end
end Negativity
