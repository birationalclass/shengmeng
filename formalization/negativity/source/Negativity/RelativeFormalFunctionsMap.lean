module

public import Negativity.AffineFormalFunctions
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

/-- The actual base change of a base ideal-power thickening. The source
scheme is arbitrary and is not required to be affine. -/
def actualRelativePowerThickening {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (n : ℕ) : Scheme.{u} :=
  ((I ^ (n + 1)).comap f).subscheme

def actualRelativePowerProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (n : ℕ) :
    actualRelativePowerThickening f I n ⟶ actualPowerThickening I n :=
  IdealSheafData.subschemeMap _ _ f ((I ^ (n + 1)).le_map_comap f)

def actualRelativePowerInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) {m n : ℕ} (h : m ≤ n) :
    actualRelativePowerThickening f I m ⟶ actualRelativePowerThickening f I n :=
  IdealSheafData.inclusion (IdealSheafData.comap_mono f (by
    intro U
    simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
      (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1))))

theorem actual_relative_power_projection_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) {m n : ℕ} (h : m ≤ n) :
    actualRelativePowerInclusion f I h ≫ actualRelativePowerProjection f I n =
      actualRelativePowerProjection f I m ≫ actualPowerThickeningInclusion I h := by
  apply (cancel_mono (I ^ (n + 1)).subschemeι).mp
  simp [actualRelativePowerInclusion, actualRelativePowerProjection,
    actualPowerThickeningInclusion, Category.assoc]

/-- Compatible genuine section families on genuine schemes and genuine maps. -/
def actualCompatibleSchemeSections (Z : ℕ → Scheme.{u})
    (inc : ∀ {m n : ℕ}, m ≤ n → (Z m ⟶ Z n)) :
    Subring (∀ n : ℕ, Γ(Z n, ⊤)) where
  carrier := {a | ∀ m n (h : m ≤ n), (inc h).appTop (a n) = a m}
  zero_mem' := by intro m n h; exact map_zero _
  one_mem' := by intro m n h; exact map_one _
  add_mem' := by
    intro a b ha hb m n h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (ha m n h) (hb m n h))
  mul_mem' := by
    intro a b ha hb m n h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (ha m n h) (hb m n h))
  neg_mem' := by
    intro a ha m n h
    exact (map_neg _ _).trans (congrArg Neg.neg (ha m n h))

/-- Genuine regular functions on the relative thickenings, with compatibility
along genuine closed immersions. -/
def actualRelativeInfinitesimalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    Subring (∀ n : ℕ, Γ(actualRelativePowerThickening f I n, ⊤)) :=
  actualCompatibleSchemeSections (actualRelativePowerThickening f I)
    (fun h => actualRelativePowerInclusion f I h)

/-- Pull back an actual compatible family from the base to the arbitrary
source. Compatibility follows from the actual scheme square. -/
def actualRelativeInfinitesimalPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    actualInfinitesimalSections I →+* actualRelativeInfinitesimalSections f I where
  toFun a := ⟨fun n => (actualRelativePowerProjection f I n).appTop (a.1 n), by
    intro m n h
    have hs := congrArg (fun g : actualRelativePowerThickening f I m ⟶
      actualPowerThickening I n => g.appTop (a.1 n))
      (actual_relative_power_projection_square f I h)
    change (actualRelativePowerInclusion f I h).appTop
        ((actualRelativePowerProjection f I n).appTop (a.1 n)) =
      (actualRelativePowerProjection f I m).appTop
        ((actualPowerThickeningInclusion I h).appTop (a.1 n)) at hs
    rw [a.2 m n h] at hs
    exact hs⟩
  map_one' := by apply Subtype.ext; funext n; simp
  map_mul' a b := by apply Subtype.ext; funext n; simp
  map_zero' := by apply Subtype.ext; funext n; simp
  map_add' a b := by apply Subtype.ext; funext n; simp

/-- The canonical completion comparison for an affine base and an arbitrary,
possibly nonaffine source. Its construction supplies no bijectivity claim. -/
def actualRelativeFormalFunctionsMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (I : Y.IdealSheafData) :
    AdicCompletion (I.ideal ⟨⊤, isAffineOpen_top Y⟩) Γ(Y, ⊤) →+*
      actualRelativeInfinitesimalSections f I :=
  (actualRelativeInfinitesimalPullback f I).comp (actualAffineFormalFunctionsMap Y I)

/-- Final theorem: the genuine relative comparison evaluates by actual
pullback on every base thickening and sends a completed constant to its
actual restriction on every relative thickening. No source affineness,
comparison map or compatibility premise is supplied. Proper formal
functions still requires proving that this constructed map is bijective. -/
theorem actual_relative_formal_functions_evaluation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData) :
    (∀ (a : AdicCompletion (I.ideal ⟨⊤, isAffineOpen_top Y⟩) Γ(Y, ⊤)) (n : ℕ),
      (actualRelativeFormalFunctionsMap f I a).1 n =
        (actualRelativePowerProjection f I n).appTop
          ((actualAffineThickeningSectionsEquiv Y I n).symm
            (AdicCompletion.evalₐ _ (n + 1) a))) ∧
    (∀ (r : Γ(Y, ⊤)) (n : ℕ),
      (actualRelativeFormalFunctionsMap f I (AdicCompletion.of _ Γ(Y, ⊤) r)).1 n =
        ((I ^ (n + 1)).comap f).subschemeι.appTop (f.appTop r)) := by
  constructor
  · intro a n; rfl
  · intro r n
    change (actualRelativePowerProjection f I n).appTop
      ((actualAffineThickeningSectionsEquiv Y I n).symm
        (AdicCompletion.evalₐ _ (n + 1) (AdicCompletion.of _ Γ(Y, ⊤) r))) = _
    rw [AdicCompletion.evalₐ_of]
    have he : (actualAffineThickeningSectionsEquiv Y I n).symm
        (Ideal.Quotient.mk _ r) = (I ^ (n + 1)).subschemeι.appTop r := by
      apply (actualAffineThickeningSectionsEquiv Y I n).injective
      rw [RingEquiv.apply_symm_apply, actual_affine_thickening_sections_pullback]
    rw [he]
    have hs : actualRelativePowerProjection f I n ≫ (I ^ (n + 1)).subschemeι =
        ((I ^ (n + 1)).comap f).subschemeι ≫ f :=
      IdealSheafData.subschemeMap_subschemeι ((I ^ (n + 1)).comap f)
        (I ^ (n + 1)) f ((I ^ (n + 1)).le_map_comap f)
    exact congrArg (fun g : actualRelativePowerThickening f I n ⟶ Y => g.appTop r) hs

end
end Negativity
