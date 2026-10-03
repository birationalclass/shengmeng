module

public import Negativity.HartshorneCartierModification
public import Negativity.ActualNegativityAffineSections
public import Negativity.CanonicalCartierPushPull
public import Negativity.BirationalCycleComposition
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual proper real-Cartier negativity (1) over an
actual affine normal base, in arbitrary characteristic. Hartshorne's
normal modification and its actual Cartier affine sections are outputs;
nefness, actual push-pull and effective pushforward perform descent.
No projectivity, modification, E, curve, section or geometric identity
is supplied as a hypothesis. -/
theorem actual_proper_affine_negativity_part_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hpush : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (d t))))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t)) :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  classical
  obtain ⟨N, π, hint, hnoeth, hnN, hπ, hbir, hsur, _, A₀, ⟨S⟩⟩ :=
    exists_actual_hartshorne_cartier_modification k b f
  have : IsIntegral N := hint
  have : IsLocallyNoetherian N := hnoeth
  have : IsProper π := hπ
  have : IsDominant π := birationalMorphism_dominant π hbir
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (π ≫ f)
  let B t := actualCartierPullback π (A t)
  let E := ∑ t, (B t).weightedWeilCycle hnN (d t)
  let D := ∑ t, (A t).weightedWeilCycle hnX (d t)
  have hmap : AlgebraicCycle.map π Order.coheight Order.coheight E = D :=
    actual_canonical_real_cartier_push_pull hnN hnX π hbir A d
  have hE : AlgebraicCycle.IsWeilDivisor E := by
    simpa [E] using cartierAtlas_real_sum_isWeilDivisor N hnN B d Finset.univ
  have hcomp : BirationalMorphism (π ≫ f) := actual_birational_morphism_comp π f hbir hf
  have hp : CycleEffective (AlgebraicCycle.map (π ≫ f) Order.coheight Order.coheight E) := by
    rw [actual_proper_birational_weil_pushforward_comp hnX hnY π hbir f hf E hE, hmap]
    exact hpush
  have hn : ActualRelativeNef k ((π ≫ f) ≫ b) (π ≫ f) B (fun t => -d t) := by
    simpa only [Category.assoc] using
      actual_relative_nef_canonical_pullback k (f ≫ b) f π A (fun t => -d t) hnef
  have hall := actual_negativity_of_affine_section_cover k b (π ≫ f) hcomp hnN hnY B d hp hn A₀ S
  have he : CycleEffective E := by
    intro z
    simpa [E, CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle] using hall z
  have hd : CycleEffective D := by
    rw [← hmap]
    exact scheme_cycle_map_effective π Order.coheight Order.coheight E he
  intro x
  simpa [D, CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle] using hd x

end
end Negativity
