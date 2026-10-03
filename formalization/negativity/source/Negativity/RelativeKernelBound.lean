module

public import Negativity.RelativeKernelFiniteness
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

/-- Final theorem: for the actual proper birational morphism over any
affine finite-type integral variety over a perfect field, the kernel of
restriction to higher actual infinitesimal thickenings is uniformly
bounded by the base ideal powers. Both the graded finite-generation and
stability proofs are internal, including the zero-ideal case. -/
theorem actual_relative_kernel_uniform_bound
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (k : Type u) [Field k] [PerfectField k]
    [Algebra k Γ(Y, ⊤)] [Algebra.FiniteType k Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (I : Y.IdealSheafData) :
    ∃ c : ℕ, ∀ n, RingHom.ker (actualRelativeRestriction f I (n + c)) ≤
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ (n + 1) := by
  let R := Γ(Y, ⊤)
  let J := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  let F := actualRelativeKernelFiltration f I
  have hk := (actual_relative_kernel_filtration f I).2.1
  by_cases hJ : J = ⊥
  · have hI : I = ⊥ := by
      apply le_antisymm (IdealSheafData.le_of_isAffine ?_) bot_le
      change J ≤ (⊥ : Ideal R)
      rw [hJ]
    have : IsDominant f := birationalMorphism_dominant f hf
    have : IsSchemeTheoreticallyDominant f := .of_isDominant f
    refine ⟨0, fun n => ?_⟩
    rw [← hk]
    have hp : I ^ (n + 1) = ⊥ := by
      ext U
      simp only [IdealSheafData.ideal_pow, Pi.pow_apply, hI,
        IdealSheafData.ideal_bot]
      simp
    simp only [actualRelativeKernelFiltration, actualRelativeKernelIdeal, hp,
      IdealSheafData.comap_bot, IdealSheafData.map_bot, f.ker_eq_bot,
      IdealSheafData.ideal_bot]
    change (⊥ : Ideal R) ≤ _
    exact bot_le
  · have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    have : Module.Finite (reesAlgebra J) F.submodule :=
      actual_relative_kernel_rees_module_finite k f hf I hJ
    have hstable : F.Stable :=
      (F.submodule_fg_iff_stable (fun n => IsNoetherian.noetherian (F.N n))).mp
        (Module.Finite.iff_fg.mp inferInstance)
    let G := J.stableFiltration (⊤ : Submodule R R)
    obtain ⟨c, hc⟩ := hstable.exists_forall_le (F' := G) (by
      simp [G, Ideal.stableFiltration])
    refine ⟨c, fun n => ?_⟩
    rw [← hk]
    have hn := hc (n + 1)
    have hg : G.N (n + 1) = J ^ (n + 1) := by
      change J ^ (n + 1) • (⊤ : Submodule R R) = _
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [hg] at hn
    change F.N ((n + c) + 1) ≤ J ^ (n + 1)
    have hi : (n + c) + 1 = (n + 1) + c := by omega
    rw [hi]
    exact hn

end
end Negativity
