module

public import Negativity.ActualRelativeCechMultiplication
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_relative_ideal_section_mul_mem {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m)
    (V : X.affineOpens) (a : Γ(X, V.1))
    (ha : a ∈ ((I ^ n).comap f).ideal V) :
    actualSectionRestriction X le_top (f.appTop r) * a ∈
      ((I ^ (m + n)).comap f).ideal V := by
  have hs : actualSectionRestriction X le_top (f.appTop r) ∈
      ((I ^ m).comap f).ideal V :=
    actual_base_ideal_local_pullback_mem f (I ^ m) r hr V
  have hm : ((I ^ (m + n)).comap f).ideal V =
      ((I ^ m).comap f).ideal V * ((I ^ n).comap f).ideal V := by
    rw [pow_add, actual_ideal_pullback_mul_over_affine_base]
    rfl
  rw [hm]
  exact Ideal.mul_mem_mul hs ha

def actualRelativeCechGradedKernel {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens) (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m) :
    (actualCechPullbackZero ((I ^ n).comap f).subschemeι (fun j => (U j).1)).ker →+
      (actualCechPullbackZero ((I ^ (m + n)).comap f).subschemeι
        (fun j => (U j).1)).ker :=
  ((actualCechScaleZero X (fun j => (U j).1) (f.appTop r)).comp
    (actualCechPullbackZero ((I ^ n).comap f).subschemeι
      (fun j => (U j).1)).ker.subtype).codRestrict _ (by
        intro a
        funext j
        change ((I ^ (m + n)).comap f).subschemeι.app (U j).1
          (actualSectionRestriction X le_top (f.appTop r) * a.1 j) = 0
        have ha : a.1 j ∈ ((I ^ n).comap f).ideal (U j) := by
          rw [← IdealSheafData.ker_subschemeι_app]
          exact congrArg (fun t : actualCechZero ((I ^ n).comap f).subscheme
            (fun j => ((I ^ n).comap f).subschemeι ⁻¹ᵁ (U j).1) => t j) a.2
        have hp := actual_relative_ideal_section_mul_mem f I m n r hr (U j) (a.1 j) ha
        rw [← IdealSheafData.ker_subschemeι_app] at hp
        exact hp)

def actualRelativeCechGradedCycle {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m) :
    actualClosedCechCocycles ((I ^ n).comap f).subschemeι (fun j => (U j).1) →+
      actualClosedCechCocycles ((I ^ (m + n)).comap f).subschemeι
        (fun j => (U j).1) :=
  ((actualCechScaleOne X (fun j => (U j).1) (f.appTop r)).comp
    (actualClosedCechCocycles ((I ^ n).comap f).subschemeι
      (fun j => (U j).1)).subtype).codRestrict _ (by
        intro a
        exact actual_relative_cech_graded_cocycle_multiplication
          f I (fun j => (U j).1) hU m n r hr a)

def actualRelativeCechGradedHOne {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m) :
    actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1) →+
      actualClosedCechHOne ((I ^ (m + n)).comap f).subschemeι
        (fun j => (U j).1) :=
  QuotientAddGroup.map (actualClosedCechBoundary ((I ^ n).comap f).subschemeι
    (fun j => (U j).1)).range
    (actualClosedCechBoundary ((I ^ (m + n)).comap f).subschemeι
      (fun j => (U j).1)).range (actualRelativeCechGradedCycle f I U hU m n r hr) (by
        rintro a ⟨c, rfl⟩
        refine ⟨actualRelativeCechGradedKernel f I U m n r hr c, ?_⟩
        apply Subtype.ext
        exact actual_cech_difference_scale X (fun j => (U j).1) (f.appTop r) c.1)

/-- Final theorem: multiplication by an actual coefficient in I^m
descends to actual first Cech cohomology of I^n O_X with target degree
m+n. Compatibility with actual boundaries is proved internally. This is
the homogeneous Rees action; no finite-generation hypothesis is supplied
and finite generation is not established by this theorem. -/
theorem actual_relative_cech_graded_action_on_classes
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m)
    (a : actualClosedCechCocycles ((I ^ n).comap f).subschemeι (fun j => (U j).1)) :
    actualRelativeCechGradedHOne f I U hU m n r hr
      (QuotientAddGroup.mk' _ a) =
        QuotientAddGroup.mk' _ (actualRelativeCechGradedCycle f I U hU m n r hr a) := rfl

end
end Negativity
