module

public import Negativity.CartierPullback
public import Negativity.CodimensionOne
public import Negativity.FiniteNormalGeometry
public import Negativity.Descent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- A rational equation is a unit at x when it is the image of an actual
unit in the scheme's local ring. -/
def RationalUnitAt (X : Scheme) [IsIntegral X] (x : X) (a : X.functionFieldˣ) : Prop :=
  ∃ u : (X.presheaf.stalk x)ˣ,
    Units.map (algebraMap (X.presheaf.stalk x) X.functionField : _ →* _) u = a

/-- Unit transition functions do not change the vanishing support. -/
theorem rationalUnitAt_unit_transition (X : Scheme) [IsIntegral X]
    (x : X) (a : X.functionFieldˣ) (u : (X.presheaf.stalk x)ˣ) :
    RationalUnitAt X x
      (Units.map (algebraMap (X.presheaf.stalk x) X.functionField : _ →* _) u * a) ↔
      RationalUnitAt X x a := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨u⁻¹ * v, ?_⟩
    rw [map_mul, hv, map_inv]
    group
  · rintro ⟨v, rfl⟩
    exact ⟨u * v, map_mul _ _ _⟩

/-- The support of an actual Cartier presentation, including points in all
codimensions. It is defined by local units, not by chosen coefficient sets. -/
noncomputable def CartierAtlas.vanishingSupport {X : Scheme} [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) : Set X :=
  {x | ¬ RationalUnitAt X x (A.equation (A.covers x).choose)}

theorem cartierAtlas_support_eq_on_chart (X : Scheme) [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) (i : ι) (x : X) (hx : x ∈ A.chart i) :
    x ∈ A.vanishingSupport ↔ ¬ RationalUnitAt X x (A.equation i) := by
  obtain ⟨u, hu⟩ := A.transition i _ x hx (A.covers x).choose_spec
  change (¬ RationalUnitAt X x (A.equation (A.covers x).choose)) ↔ _
  rw [← hu, rationalUnitAt_unit_transition]

/-- Effective Cartier equations are regular in the actual local rings.
This is the local definition of effectivity, not a desired support identity. -/
def CartierAtlas.Effective {X : Scheme} [IsIntegral X] {ι : Type*}
    (A : CartierAtlas X ι) : Prop :=
  ∀ i (x : X), x ∈ A.chart i →
    ∃ r : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField r = (A.equation i : X.functionField)

theorem rationalUnitAt_regular_iff (X : Scheme) [IsIntegral X] (x : X)
    (a : X.functionFieldˣ) (r : X.presheaf.stalk x)
    (hr : algebraMap (X.presheaf.stalk x) X.functionField r = (a : X.functionField)) :
    RationalUnitAt X x a ↔ IsUnit r := by
  constructor
  · rintro ⟨u, hu⟩
    have he : (u : X.presheaf.stalk x) = r := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      exact (congrArg Units.val hu).trans hr.symm
    exact he ▸ u.isUnit
  · rintro ⟨u, rfl⟩
    exact ⟨u, Units.ext hr⟩

/-- A local Scheme map reflects units. For regular equations, this gives
the actual inverse-image support statement even in exceptional fibers. -/
theorem rationalUnitAt_regular_pullback_iff {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (x : X) (a : Y.functionFieldˣ) (r : Y.presheaf.stalk (f x))
    (hr : algebraMap (Y.presheaf.stalk (f x)) Y.functionField r = (a : Y.functionField)) :
    RationalUnitAt X x (Units.map (dominantFunctionFieldMap f : _ →* _) a) ↔
      RationalUnitAt Y (f x) a := by
  have hs : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) =
      dominantFunctionFieldMap f (a : Y.functionField) := by
    rw [← dominantFunctionFieldMap_stalk f x r, hr]
  rw [rationalUnitAt_regular_iff X x _ _ hs,
    rationalUnitAt_regular_iff Y (f x) a r hr]
  exact isUnit_map_iff (f.stalkMap x).hom r

/-- Construction of an effective Cartier pullback together with its actual
support as the inverse image. The pullback and support equality are outputs. -/
theorem exists_effective_cartierAtlas_pullback_support {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    {ι : Type*} (A : CartierAtlas Y ι) (hA : A.Effective) :
    ∃ B : CartierAtlas X X, B.Effective ∧
      B.vanishingSupport = f ⁻¹' A.vanishingSupport ∧
      ∀ z : X, B.equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
        (A.equation (A.covers (f z)).choose) := by
  classical
  obtain ⟨B, hB⟩ := exists_cartierAtlas_pullback f A
  have heffective : B.Effective := by
    intro z x hx
    obtain ⟨r, hr⟩ := hA _ (f x) ((hB z).1 hx)
    refine ⟨(f.stalkMap x).hom r, ?_⟩
    rw [(hB z).2.2]
    rw [← dominantFunctionFieldMap_stalk f x r, hr]
    rfl
  refine ⟨B, heffective, ?_, fun z => (hB z).2.2⟩
  ext x
  rw [cartierAtlas_support_eq_on_chart X B x x (hB x).2.1,
    Set.mem_preimage, cartierAtlas_support_eq_on_chart Y A _ (f x) (A.covers (f x)).choose_spec,
    (hB x).2.2]
  obtain ⟨r, hr⟩ := hA _ (f x) (A.covers (f x)).choose_spec
  exact not_congr (rationalUnitAt_regular_pullback_iff f x _ r hr)

/-- Local effectivity produces nonnegative actual codimension-one Weil
coefficients, rather than supplying cycle effectivity as a bridge input. -/
theorem effective_cartierAtlas_weil_nonneg (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective) :
    ∀ x : X, 0 ≤ A.weilCycle hn x := by
  classical
  intro x
  by_cases hx : Order.coheight x = 1
  · obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨r, hr⟩ := hA i x hi
    have := hn x
    have := normal_codimensionOne_stalk_isDVR X x hx
    change 0 ≤ A.coefficient hn x
    rw [cartierAtlas_coefficient_eq X hn A i x hx hi]
    have hne : r ≠ 0 := by
      intro hz
      exact (A.equation i).ne_zero (by simpa [hz] using hr.symm)
    unfold schemeRationalOrder
    rw [dvr_rationalOrder_represents _ _ _ r 1 hne one_ne_zero (by simpa using hr.symm)]
    simp [LocalFractionOrder]
  · simp [CartierAtlas.weilCycle, CartierAtlas.coefficient, hx]

/-- For a proper birational modification, the constructed effective Cartier
pullback reflects both fiber-support alternatives. Surjectivity and support
pullback are proved from geometry, not supplied as descent inputs. This does
not assume or prove that either fiber-support alternative always holds. -/
theorem exists_effective_cartierAtlas_fiber_descent {X X' : Scheme}
    [IsIntegral X] [IsIntegral X'] (p : X' ⟶ X) [IsProper p]
    (hp : BirationalMorphism p) {ι : Type*} (A : CartierAtlas X ι)
    (hA : A.Effective) :
    ∃ B : CartierAtlas X' X', B.Effective ∧
      ∀ (T : Type*) (f : X → T) (y : T),
        (Disjoint {x' | f (p x') = y} B.vanishingSupport ∨
          {x' | f (p x') = y} ⊆ B.vanishingSupport) ↔
        (Disjoint {x | f x = y} A.vanishingSupport ∨
          {x | f x = y} ⊆ A.vanishingSupport) := by
  have := birationalMorphism_dominant p hp
  obtain ⟨B, hB, hs, _⟩ := exists_effective_cartierAtlas_pullback_support p A hA
  have hsurj : Function.Surjective p := (proper_birational_surjective p hp).1
  refine ⟨B, hB, ?_⟩
  intro T f y
  rw [hs, composite_fiber, ← disjoint_iff_preimage_disjoint p hsurj,
    ← subset_iff_preimage_subset p hsurj]

end Negativity
