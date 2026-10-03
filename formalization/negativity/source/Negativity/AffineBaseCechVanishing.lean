module
public import Negativity.AffineBaseReesCoordinates
public import Negativity.RelativeCechSectionLifting
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualIdealFamilyCechKernelVanishing {X : Scheme.{u}}
    (K : ℕ → X.IdealSheafData) (hK : Antitone K)
    {ι : Type v} (U : ι → X.affineOpens) (c : ℕ) : Prop :=
  ∀ n (q : actualClosedCechHOne (K (n + c + 1)).subschemeι (fun j => (U j).1)),
    actualClosedCechForget (K (n + c + 1)).subschemeι (fun j => (U j).1) q = 0 →
    actualClosedCechHOneTransition
      (IdealSheafData.inclusion (hK (show n + 1 ≤ n + c + 1 by omega)))
      (K (n + c + 1)).subschemeι (fun j => (U j).1) q = 0

theorem actual_ideal_family_cech_kernel_vanishing_congr {X : Scheme.{u}}
    (K L : ℕ → X.IdealSheafData) (hK : Antitone K) (hL : Antitone L)
    (he : K = L) {ι : Type v} (U : ι → X.affineOpens) (c : ℕ) :
    actualIdealFamilyCechKernelVanishing K hK U c =
      actualIdealFamilyCechKernelVanishing L hL U c := by
  subst L
  rfl

theorem actual_relative_power_ideal_antitone {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) : Antitone (fun n : ℕ => (J ^ n).comap f) := by
  intro m n hmn
  apply IdealSheafData.comap_mono
  intro V
  simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
    Ideal.pow_le_pow_right (I := J.ideal V) hmn

/-- Final theorem: the actual Cech transition-vanishing bound is unchanged
when an affine base is written as Spec of its functions. Actual ideal
pullback identities identify all thickenings and all transition maps. -/
theorem actual_affine_base_cech_kernel_vanishing
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens) (c : ℕ)
    (h : ActualRelativeCechKernelVanishing (f ≫ Y.toSpecΓ)
      (actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) U c) :
    ActualRelativeCechKernelVanishing f J U c := by
  let K : ℕ → X.IdealSheafData := fun n =>
    ((actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) ^ n).comap
      (f ≫ Y.toSpecΓ)
  let L : ℕ → X.IdealSheafData := fun n => (J ^ n).comap f
  have hK : Antitone K := actual_relative_power_ideal_antitone _ _
  have hL : Antitone L := actual_relative_power_ideal_antitone _ _
  have he : K = L := funext (fun n => actual_affine_base_spec_power_pullback f J n)
  change actualIdealFamilyCechKernelVanishing K hK U c at h
  change actualIdealFamilyCechKernelVanishing L hL U c
  rw [← actual_ideal_family_cech_kernel_vanishing_congr K L hK hL he U c]
  exact h

end
end Negativity
