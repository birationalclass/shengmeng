module

public import Negativity.RelativeKernelBound
public import Negativity.AdicComparisonInjectivity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the canonical actual relative formal-functions
comparison is injective for proper birational morphisms over affine
finite-type integral varieties over a perfect field. The source is
arbitrary and need not be affine; the actual uniform kernel bound is
proved internally. Surjectivity remains a separate geometric task. -/
theorem actual_relative_formal_functions_injective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (k : Type u) [Field k] [PerfectField k]
    [Algebra k Γ(Y, ⊤)] [Algebra.FiniteType k Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) :
    Function.Injective (actualRelativeFormalFunctionsMap f I) := by
  obtain ⟨c, hc⟩ := actual_relative_kernel_uniform_bound k f hf I
  let K := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  let B (n : ℕ) : Type u := Γ(actualRelativePowerThickening f I n, ⊤)
  let t {m n : ℕ} (h : m ≤ n) : B n →+* B m :=
    (actualRelativePowerInclusion f I h).appTop.hom
  let q (n : ℕ) : (Γ(Y, ⊤) ⧸ K ^ (n + 1)) →+* B n :=
    actualRelativeQuotientMap f I n
  have hq : ∀ {m n : ℕ} (h : m ≤ n) (a : Γ(Y, ⊤) ⧸ K ^ (n + 1)),
      t h (q n a) = q m (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) a) :=
    fun h a => actual_relative_quotient_map_transition f I h a
  change Function.Injective (adicApproximationComparison K B t q hq)
  apply adic_comparison_injective_of_uniform_kernel_bound K B t q hq c
  intro n r hr
  apply hc n
  change actualRelativeRestriction f I (n + c) r = 0
  exact (actual_relative_quotient_map_constant f I (n + c) r).symm.trans hr

end
end Negativity
