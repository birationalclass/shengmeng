module
public import Mathlib.Algebra.Module.GradedModule

@[expose] public section
namespace Negativity
open GradedMonoid
universe u v w
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A genuine homogeneous quotient action inherits all graded module axioms
from the source, using only the proved componentwise quotient surjections. -/
def actualGradedModuleOfSurjective
    {A : ℕ → Type u} {M : ℕ → Type v} {N : ℕ → Type w}
    [∀ n, AddCommMonoid (A n)] [∀ n, AddCommMonoid (M n)]
    [∀ n, AddCommMonoid (N n)] [GMonoid A] [DirectSum.Gmodule A M]
    [GSMul A N]
    (q : ∀ n, M n →+ N n) (hq : ∀ n, Function.Surjective (q n))
    (hsmul : ∀ (i j : ℕ) (a : A i) (m : M j),
      q (i + j) (GSMul.smul a m) = GSMul.smul a (q j m)) :
    DirectSum.Gmodule A N := by
  let qs : GradedMonoid M → GradedMonoid N := fun x => ⟨x.1, q x.1 x.2⟩
  have hqs (a : GradedMonoid A) (b : GradedMonoid M) :
      qs (a • b) = a • qs b := by
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    exact congrArg (Sigma.mk (i + j)) (hsmul i j a b)
  refine {
    smul := GSMul.smul
    one_smul := ?_
    mul_smul := ?_
    smul_add := ?_
    smul_zero := ?_
    add_smul := ?_
    zero_smul := ?_ }
  · rintro ⟨n, b⟩
    obtain ⟨c, rfl⟩ := hq n b
    exact (hqs 1 ⟨n, c⟩).symm.trans
      (congrArg qs (GMulAction.one_smul ⟨n, c⟩))
  · intro a a'
    rintro ⟨n, b⟩
    obtain ⟨c, rfl⟩ := hq n b
    calc
      (a * a') • qs ⟨n, c⟩ = qs ((a * a') • ⟨n, c⟩) := (hqs _ _).symm
      _ = qs (a • a' • ⟨n, c⟩) := congrArg qs (GMulAction.mul_smul a a' ⟨n, c⟩)
      _ = a • a' • qs ⟨n, c⟩ := by rw [hqs, hqs]
  · intro i j a b c
    obtain ⟨b', rfl⟩ := hq j b
    obtain ⟨c', rfl⟩ := hq j c
    rw [← map_add, ← hsmul, DirectSum.GdistribMulAction.smul_add,
      map_add, hsmul, hsmul]
  · intro i j a
    rw [← (q j).map_zero, ← hsmul, DirectSum.GdistribMulAction.smul_zero, map_zero]
  · intro i j a a' b
    obtain ⟨b', rfl⟩ := hq j b
    rw [← hsmul, DirectSum.Gmodule.add_smul, map_add, hsmul, hsmul]
  · intro i j b
    obtain ⟨b', rfl⟩ := hq j b
    rw [← hsmul, DirectSum.Gmodule.zero_smul, map_zero]

#print axioms actualGradedModuleOfSurjective
end
end Negativity
