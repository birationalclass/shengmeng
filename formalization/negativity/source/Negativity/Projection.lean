module

public import Negativity.GeometricCycles
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
open Function.locallyFinsuppWithin

/-- Pushforward of a single generic-point cycle in mathlib's actual Scheme API. -/
theorem scheme_cycle_map_single {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    [DecidableEq X] [DecidableEq Y] (x : X) (a : ℝ) :
    AlgebraicCycle.map f wx wy (single x a) =
      single (f.base x) (a * (AlgebraicCycle.mapCoeff f wx wy x : ℝ)) := by
  ext y
  change (∑ᶠ z ∈ f.base ⁻¹' {y}, single x a z *
    (AlgebraicCycle.mapCoeff f wx wy z : ℝ)) = _
  rw [finsum_eq_single _ x (by intro z hz; simp [single_apply, hz])]
  by_cases hy : y = f.base x <;> simp [single_apply, hy, eq_comm]

/-- A single component of equal weight pushes to residue-degree times its image. -/
theorem scheme_curve_push_of_same_weight {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    [DecidableEq X] [DecidableEq Y] (x : X) (h : wx x = wy (f.base x)) :
    AlgebraicCycle.map f wx wy (single x (1 : ℝ)) =
      f.residueDegree x • single (f.base x) (1 : ℝ) := by
  rw [scheme_cycle_map_single, scheme_mapCoeff_of_same_weight f wx wy x h]
  ext y
  by_cases hy : y = f.base x <;> simp [single_apply, hy]

/-- A single component whose weight drops has zero pushforward. -/
theorem scheme_curve_push_of_drop {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    [DecidableEq X] [DecidableEq Y] (x : X) (h : wx x ≠ wy (f.base x)) :
    AlgebraicCycle.map f wx wy (single x (1 : ℝ)) = 0 := by
  rw [scheme_cycle_map_single, scheme_mapCoeff_zero_of_drop f wx wy x h]
  simp

/-- With Cartier/intersection compatibility left explicit, actual cycle pushforward
derives the two projection cases; no separate disjunction or scalar input is assumed.
Weights must encode curve/image dimensions in a geometric application. -/
theorem projection_cases_from_cycle_push {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    [DecidableEq X] [DecidableEq Y]
    (down : AlgebraicCycle Y ℝ →+ ℝ)
    (up : AlgebraicCycle X ℝ →+ ℝ) (x : X)
    (hcompat : up (single x 1) = down (AlgebraicCycle.map f wx wy (single x 1))) :
    (wx x ≠ wy (f.base x) ∧ up (single x 1) = 0) ∨
      (wx x = wy (f.base x) ∧
        up (single x 1) = (f.residueDegree x : ℝ) * down (single (f.base x) 1)) := by
  by_cases h : wx x = wy (f.base x)
  · right
    refine ⟨h, ?_⟩
    rw [hcompat, scheme_curve_push_of_same_weight f wx wy x h, map_nsmul]
    simp [nsmul_eq_mul]
  · left
    refine ⟨h, ?_⟩
    rw [hcompat, scheme_curve_push_of_drop f wx wy x h, map_zero]

/-- Nonpositive intersection transports along the actual Scheme-cycle map, provided
equal-weight images are admissible test curves. Cartier compatibility remains explicit. -/
theorem nonpositive_pullback_from_cycle_push {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    [DecidableEq X] [DecidableEq Y]
    (down : AlgebraicCycle Y ℝ →+ ℝ)
    (up : AlgebraicCycle X ℝ →+ ℝ) (testUp : Set X) (testDown : Set Y)
    (hcompat : ∀ x ∈ testUp,
      up (single x 1) = down (AlgebraicCycle.map f wx wy (single x 1)))
    (himage : ∀ x ∈ testUp, wx x = wy (f.base x) → f.base x ∈ testDown)
    (hnef : ∀ y ∈ testDown, down (single y 1) ≤ 0) :
    ∀ x ∈ testUp, up (single x 1) ≤ 0 := by
  intro x hx
  rcases projection_cases_from_cycle_push f wx wy down up x (hcompat x hx) with
    ⟨_, hzero⟩ | ⟨hweight, heq⟩
  · exact le_of_eq hzero
  · rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hnef _ (himage x hx hweight))

/-- Real linear extension of a projection identity from a specified generating set.
In a geometric application the set consists of Cartier divisors; the maps must be the
actual pullback and intersection maps. This theorem does not construct those maps. -/
theorem projection_formula_on_real_span {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (pull : V →ₗ[ℝ] W) (down : V →ₗ[ℝ] ℝ) (up : W →ₗ[ℝ] ℝ)
    (cartier : Set V) (hcartier : ∀ D ∈ cartier, up (pull D) = down D)
    (D : V) (hD : D ∈ Submodule.span ℝ cartier) : up (pull D) = down D := by
  exact LinearMap.eqOn_span (f := up.comp pull) (g := down) hcartier hD

/-- The actual scheme-cycle pushforward already preserves effectivity, so
only the geometric push-pull identity is left as a map-property input. -/
theorem scheme_effective_descends {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (D : AlgebraicCycle Y ℝ) (lifted : AlgebraicCycle X ℝ)
    (hleft : AlgebraicCycle.map f wx wy lifted = D)
    (hlifted : CycleEffective lifted) : CycleEffective D := by
  rw [← hleft]
  exact scheme_cycle_map_effective f wx wy lifted hlifted
end Negativity
