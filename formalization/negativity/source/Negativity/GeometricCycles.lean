module

public import Negativity.Descent
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory

/-- Effectivity for actual mathlib scheme cycles, rather than a chosen coefficient model. -/
def CycleEffective {X : Scheme} (c : AlgebraicCycle X ℝ) : Prop := ∀ x, 0 ≤ c x

/-- The actual scheme-cycle map preserves nonnegative real coefficients. -/
theorem scheme_cycle_map_effective {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (c : AlgebraicCycle X ℝ) (hc : CycleEffective c) :
    CycleEffective (AlgebraicCycle.map f wx wy c) := by
  intro y
  change 0 ≤ ∑ᶠ x ∈ f.base ⁻¹' {y}, c x * (AlgebraicCycle.mapCoeff f wx wy x : ℝ)
  apply finsum_nonneg
  intro x
  apply finsum_nonneg
  intro _
  exact mul_nonneg (hc x) (Nat.cast_nonneg _)

/-- A dimension/weight drop has zero multiplicity in actual cycle pushforward. -/
theorem scheme_mapCoeff_zero_of_drop {X Y : Scheme} (f : X ⟶ Y)
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) (x : X)
    (h : wx x ≠ wy (f.base x)) : AlgebraicCycle.mapCoeff f wx wy x = 0 := by
  simp [AlgebraicCycle.mapCoeff, h]

/-- A component of unchanged weight has residue-field degree as its multiplicity. -/
theorem scheme_mapCoeff_of_same_weight {X Y : Scheme} (f : X ⟶ Y)
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) (x : X)
    (h : wx x = wy (f.base x)) :
    AlgebraicCycle.mapCoeff f wx wy x = f.residueDegree x := by
  simp [AlgebraicCycle.mapCoeff, h]

/-- A cycle whose every nonzero component drops weight pushes to zero. -/
theorem scheme_cycle_map_zero_of_drop {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (c : AlgebraicCycle X ℝ)
    (h : ∀ x, c x ≠ 0 → wx x ≠ wy (f.base x)) :
    AlgebraicCycle.map f wx wy c = 0 := by
  have hz : ∀ x, c x * (AlgebraicCycle.mapCoeff f wx wy x : ℝ) = 0 := by
    intro x
    by_cases hx : c x = 0
    · simp [hx]
    · simp [scheme_mapCoeff_zero_of_drop f wx wy x (h x hx)]
  ext y
  simp [AlgebraicCycle.map, Function.locallyFinsupp.map, hz]

end Negativity
