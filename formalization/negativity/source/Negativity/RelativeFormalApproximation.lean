module

public import Negativity.RelativeFormalFunctionsMap
public import Negativity.AdicApproximationComparison
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The actual global-function restriction to the actual relative thickening. -/
def actualRelativeRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (n : ℕ) :
    Γ(Y, ⊤) →+* Γ(actualRelativePowerThickening f I n, ⊤) :=
  (((I ^ (n + 1)).comap f).subschemeι.appTop).hom.comp f.appTop.hom

def actualRelativeQuotientMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (I : Y.IdealSheafData) (n : ℕ) :
    (Γ(Y, ⊤) ⧸ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ (n + 1)) →+*
      Γ(actualRelativePowerThickening f I n, ⊤) :=
  (actualRelativePowerProjection f I n).appTop.hom.comp
    (actualAffineThickeningSectionsEquiv Y I n).symm.toRingHom

theorem actual_relative_quotient_map_constant {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData) (n : ℕ) (r : Γ(Y, ⊤)) :
    actualRelativeQuotientMap f I n (Ideal.Quotient.mk _ r) =
      actualRelativeRestriction f I n r := by
  have hc := (actual_relative_formal_functions_evaluation f I).2 r n
  change (actualRelativePowerProjection f I n).appTop
    ((actualAffineThickeningSectionsEquiv Y I n).symm
      (AdicCompletion.evalₐ _ (n + 1) (AdicCompletion.of _ Γ(Y, ⊤) r))) = _ at hc
  rw [AdicCompletion.evalₐ_of] at hc
  exact hc

theorem actual_relative_restriction_transition {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : Y.IdealSheafData) {m n : ℕ} (h : m ≤ n) (r : Γ(Y, ⊤)) :
    (actualRelativePowerInclusion f I h).appTop
      (actualRelativeRestriction f I n r) = actualRelativeRestriction f I m r := by
  have hs := IdealSheafData.inclusion_subschemeι
    (IdealSheafData.comap_mono f (show I ^ (n + 1) ≤ I ^ (m + 1) from by
      intro U
      simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
        (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1))))
  exact congrArg (fun g : actualRelativePowerThickening f I m ⟶ X =>
    g.appTop (f.appTop r)) hs

theorem actual_relative_quotient_map_transition {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData) {m n : ℕ} (h : m ≤ n)
    (a : Γ(Y, ⊤) ⧸ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ (n + 1)) :
    (actualRelativePowerInclusion f I h).appTop
      (actualRelativeQuotientMap f I n a) = actualRelativeQuotientMap f I m
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) a) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [actual_relative_quotient_map_constant]
  change (actualRelativePowerInclusion f I h).appTop
    (actualRelativeRestriction f I n r) = actualRelativeQuotientMap f I m
      (Ideal.Quotient.mk _ r)
  rw [actual_relative_quotient_map_constant]
  exact actual_relative_restriction_transition f I h r

/-- Final theorem, explicitly conditional: two precise uniform
approximation bounds on actual sections imply bijectivity of the already
constructed actual relative formal-functions map. No abstract section
ring, arbitrary comparison map or compatibility identity is supplied.
Proper geometry must still establish these stated bounds. -/
theorem actual_relative_formal_functions_bijective_of_uniform_approximation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData)
    (c : ℕ)
    (hker : ∀ n (r : Γ(Y, ⊤)), actualRelativeRestriction f I (n + c) r = 0 →
      r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ (n + 1))
    (himage : ∀ n (b : Γ(actualRelativePowerThickening f I (n + c), ⊤)),
      ∃ r : Γ(Y, ⊤), actualRelativeRestriction f I n r =
        (actualRelativePowerInclusion f I (Nat.le_add_right n c)).appTop b) :
    Function.Bijective (actualRelativeFormalFunctionsMap f I) := by
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
  change Function.Bijective (adicApproximationComparison K B t q hq)
  apply adic_comparison_bijective_of_uniform_approximation K B t q hq c
  · intro n r hr
    apply hker n r
    exact (actual_relative_quotient_map_constant f I (n + c) r).symm.trans hr
  · intro n b
    obtain ⟨r, hr⟩ := himage n b
    exact ⟨r, (actual_relative_quotient_map_constant f I n r).trans hr⟩

end
end Negativity
