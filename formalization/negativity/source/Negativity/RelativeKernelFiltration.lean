module

public import Negativity.PullbackIdealProducts
public import Negativity.RelativeFormalApproximation
public import Mathlib.RingTheory.Filtration
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualRelativeKernelIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (I : Y.IdealSheafData) (n : ℕ) : Ideal Γ(Y, ⊤) :=
  (((I ^ n).comap f).map f).ideal ⟨⊤, isAffineOpen_top Y⟩

theorem actual_relative_kernel_ideal_mono {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData) (n : ℕ) :
    actualRelativeKernelIdeal f I (n + 1) ≤ actualRelativeKernelIdeal f I n := by
  have hh : I ^ (n + 1) ≤ I ^ n := by
    intro U
    simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
      (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.le_succ n))
  exact (IdealSheafData.map_mono f (IdealSheafData.comap_mono f hh))
    ⟨⊤, isAffineOpen_top Y⟩

theorem actual_relative_kernel_ideal_mul {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] (I : Y.IdealSheafData) (n : ℕ) :
    I.ideal ⟨⊤, isAffineOpen_top Y⟩ * actualRelativeKernelIdeal f I n ≤
      actualRelativeKernelIdeal f I (n + 1) := by
  have hh : I * ((I ^ n).comap f).map f ≤ ((I ^ (n + 1)).comap f).map f := by
    rw [IdealSheafData.le_map_iff_comap_le,
      actual_ideal_pullback_mul_over_affine_base, pow_succ',
      actual_ideal_pullback_mul_over_affine_base]
    intro U
    exact Ideal.mul_mono_right ((IdealSheafData.comap_map_le ((I ^ n).comap f) f) U)
  exact hh ⟨⊤, isAffineOpen_top Y⟩

/-- The actual kernel filtration, constructed by pullback of ideal powers
and scheme-theoretic pushforward. The source is arbitrary and nonaffine. -/
def actualRelativeKernelFiltration {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (I : Y.IdealSheafData) : (I.ideal ⟨⊤, isAffineOpen_top Y⟩).Filtration Γ(Y, ⊤) where
  N n := actualRelativeKernelIdeal f I n
  mono n := actual_relative_kernel_ideal_mono f I n
  smul_le n := by
    rw [Ideal.smul_eq_mul]
    exact actual_relative_kernel_ideal_mul f I n

/-- Final theorem: the constructed filtration consists of the actual
kernels of global restriction to every genuine relative power thickening,
starts at the whole base ring and satisfies the actual ideal-adic
decreasing and multiplicative filtration laws. No boundedness, stability,
finite-generation or formal-functions premise is supplied. -/
theorem actual_relative_kernel_filtration {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f] (I : Y.IdealSheafData) :
    (actualRelativeKernelFiltration f I).N 0 = ⊤ ∧
    (∀ n, (actualRelativeKernelFiltration f I).N (n + 1) =
      RingHom.ker (actualRelativeRestriction f I n)) ∧
    (∀ n, (actualRelativeKernelFiltration f I).N (n + 1) ≤
      (actualRelativeKernelFiltration f I).N n) ∧
    (∀ n, I.ideal ⟨⊤, isAffineOpen_top Y⟩ • (actualRelativeKernelFiltration f I).N n ≤
      (actualRelativeKernelFiltration f I).N (n + 1)) := by
  refine ⟨?_, ?_, (actualRelativeKernelFiltration f I).mono,
    (actualRelativeKernelFiltration f I).smul_le⟩
  · simp [actualRelativeKernelFiltration, actualRelativeKernelIdeal]
  · intro n
    change ((((I ^ (n + 1)).comap f).subschemeι ≫ f).ker).ideal
      ⟨⊤, isAffineOpen_top Y⟩ = _
    rw [Scheme.Hom.ker_apply]
    rfl

end
end Negativity
