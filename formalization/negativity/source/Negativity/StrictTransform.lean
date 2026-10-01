module

public import Negativity.CartierPushPull
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false

abbrev PrimeDivisorPoint (X : Scheme) := {x : X // Order.coheight x = 1}

/-- A strict transform is represented by the generic point of the unique
prime divisor above the target prime. Its existence comes from the actual
codimension-one isomorphism theorem, not a supplied injection. -/
noncomputable def geometricStrictTransform {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) :
    PrimeDivisorPoint Y → PrimeDivisorPoint X := fun y ↦ by
  have := hnY y
  let h := proper_birational_codimensionOne_unique_preimage f hf y y.2
  exact ⟨h.choose, h.choose_spec.2.2.1⟩

theorem geometricStrictTransform_image {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) (y : PrimeDivisorPoint Y) :
    f (geometricStrictTransform hnY f hf y) = y := by
  have := hnY y
  exact (proper_birational_codimensionOne_unique_preimage f hf y y.2).choose_spec.1

/-- The strict-transform injection is constructed from the actual morphism. -/
theorem geometricStrictTransform_injective {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) :
    Function.Injective (geometricStrictTransform hnY f hf) := by
  intro y z h
  apply Subtype.ext
  have hh := congrArg (fun x : PrimeDivisorPoint X ↦ f x) h
  simpa only [geometricStrictTransform_image] using hh

/-- A source prime is a strict transform exactly when its image is a
codimension-one point. This identifies the coefficient-model exceptional
indices with actual geometric primes contracted out of codimension one. -/
theorem geometric_exceptional_iff {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) (x : PrimeDivisorPoint X) :
    ExceptionalIndex (geometricStrictTransform hnY f hf) x ↔ Order.coheight (f x) ≠ 1 := by
  classical
  constructor
  · intro hx hy
    have := hnY (f x)
    let h := proper_birational_codimensionOne_unique_preimage f hf (f x) hy
    apply hx
    refine ⟨⟨f x, hy⟩, ?_⟩
    apply Subtype.ext
    exact (h.choose_spec.2.2.2 x rfl).symm
  · intro hy hx
    obtain ⟨y, rfl⟩ := hx
    rw [geometricStrictTransform_image] at hy
    exact hy y.2

/-- The actual Scheme-cycle pushforward reads precisely the coefficient
at the actual strict transform, with multiplicity one. -/
theorem scheme_cycle_strictTransform_coefficient {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (E : AlgebraicCycle X ℝ) (y : PrimeDivisorPoint Y) :
    AlgebraicCycle.map f Order.coheight Order.coheight E y =
      E (geometricStrictTransform hnY f hf y) := by
  classical
  have := hnY y
  let h := proper_birational_codimensionOne_unique_preimage f hf y y.2
  let x := geometricStrictTransform hnY f hf y
  have hxy : f x = y := geometricStrictTransform_image hnY f hf y
  have : IsIso (f.stalkMap (x : X)) := h.choose_spec.2.1
  change (∑ᶠ z ∈ f.base ⁻¹' {(y : Y)}, E z *
    (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight z : ℝ)) = E x
  have hsingle : ∀ z : X, z ≠ x →
      (∑ᶠ (_ : z ∈ f.base ⁻¹' {(y : Y)}), E z *
        (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight z : ℝ)) = 0 := by
    intro z hz
    have hzy : f z ≠ y := fun he ↦ hz (h.choose_spec.2.2.2 z he)
    simp [Set.mem_preimage, Set.mem_singleton_iff, hzy]
  rw [finsum_eq_single _ (x : X) hsingle]
  have hweight : Order.coheight (x : X) = Order.coheight (f x) := by rw [x.2, hxy, y.2]
  rw [scheme_mapCoeff_of_same_weight f Order.coheight Order.coheight x hweight,
    scheme_residueDegree_of_stalk_iso]
  simp [hxy]

/-- Finite-support coefficients of an actual Weil cycle on a quasi-compact
scheme, indexed by actual codimension-one generic points. -/
noncomputable def weilCycleCoefficients (X : Scheme) [CompactSpace X]
    (E : AlgebraicCycle X ℝ) : PrimeDivisorPoint X →₀ ℝ :=
  Finsupp.ofSupportFinite (fun x ↦ E x)
    (E.finite_support.preimage Subtype.val_injective.injOn)

/-- The original coefficient-model pushforward is now instantiated by
actual proper birational Scheme geometry and agrees with actual cycle push. -/
theorem weilCycleCoefficients_pushforward {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace X] [CompactSpace Y]
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) (E : AlgebraicCycle X ℝ) :
    weilCycleCoefficients Y (AlgebraicCycle.map f Order.coheight Order.coheight E) =
      birationalPush (geometricStrictTransform hnY f hf)
        (geometricStrictTransform_injective hnY f hf) (weilCycleCoefficients X E) := by
  ext y
  exact scheme_cycle_strictTransform_coefficient hnY f hf E y

end Negativity
