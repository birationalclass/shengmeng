module
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
open scoped Pointwise
/-- Artin--Rees kills all relations on a high ideal power once one ideal kills their images. -/
theorem noetherian_artinRees_kernel_restriction
    {R P N : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : P →ₗ[R] R) (g : P →ₗ[R] N)
    (hJ : J • LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : P,
      x ∈ J ^ n • (⊤ : Submodule R P) → f x = 0 → g x = 0 := by
  obtain ⟨k,hk⟩ := Ideal.exists_pow_inf_eq_pow_smul J (LinearMap.ker f)
  refine ⟨k+1, by omega, ?_⟩
  intro x hx hf
  have hx' : x ∈ J ^ (k+1) • (⊤ : Submodule R P) ⊓ LinearMap.ker f := ⟨hx,hf⟩
  rw [hk (k+1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx'
  have hle : J • (J ^ k • (⊤ : Submodule R P) ⊓ LinearMap.ker f) ≤
      J • LinearMap.ker f := smul_mono_right J inf_le_right
  exact hJ (hle hx')

/-- An injective module extends a linear map across an arbitrary map when its kernel is killed.
The intermediate map is constructed on the actual range, not supplied as a certificate. -/
theorem injective_linearMap_extend_of_ker_le
    {R P I : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup I] [Module R I] [Module.Injective R I]
    (f : P →ₗ[R] R) (g : P →ₗ[R] I)
    (hg : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ h : R →ₗ[R] I, h.comp f = g := by
  let q : LinearMap.range f →ₗ[R] I :=
    ((LinearMap.ker f).liftQ g hg).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨h,hh⟩ := Module.Injective.out (R := R) (Q := I)
    (LinearMap.range f).subtype (Submodule.subtype_injective _) q
  refine ⟨h, ?_⟩
  ext x
  change h (f x) = g x
  calc
    h (f x) = q ⟨f x, LinearMap.mem_range_self f x⟩ := hh (⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f)
    _ = g x := by simp [q, LinearMap.quotKerEquivRange_symm_apply_image]
end LinearStudy