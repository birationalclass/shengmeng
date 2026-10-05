import JordanChains
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JordanSize
variable {K V W : Type*} [Field K]
 [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Perfection is represented by the actual identification with the full dual. -/
theorem pairing_operator (T : V ≃ₗ[K] V) (S : Module.End K W)
    (e : W ≃ₗ[K] Module.Dual K V) (d : K)
    (h : ∀ x y, e (S y) (T x) = d * e y x) :
    e.toLinearMap.comp S =
      (d • T.symm.toLinearMap.dualMap).comp e.toLinearMap := by
  ext y x
  simpa using h (T.symm x) y

lemma dual_ker_finrank [FiniteDimensional K V] (D : Module.End K V) :
    Module.finrank K (LinearMap.ker D.dualMap) =
      Module.finrank K (LinearMap.ker D) := by
  have h1 := D.finrank_range_add_finrank_ker
  have h2 := D.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq] at h2
  omega

def intertwiningKerEquiv (e : V ≃ₗ[K] W)
    (D : Module.End K V) (E : Module.End K W)
    (h : ∀ x, e (D x) = E (e x)) :
    LinearMap.ker D ≃ₗ[K] LinearMap.ker E where
  toFun x := ⟨e x, by rw [LinearMap.mem_ker, ← h]; simp [x.property]⟩
  invFun y := ⟨e.symm y, by
    rw [LinearMap.mem_ker]
    apply e.injective
    rw [h]; simp [y.property]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

lemma intertwining_pow (D : Module.End K V) (E : Module.End K W)
    (L : V →ₗ[K] W) (h : ∀ x, L (D x) = E (L x)) (j : ℕ) :
    ∀ x, L ((D^j) x) = (E^j) (L x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    intro x
    simp only [pow_succ', Module.End.mul_apply, h, ih]

lemma dual_pow (D : Module.End K V) (j : ℕ) :
    (D.dualMap)^j = (D^j).dualMap := by
  induction j with
  | zero => ext f x; rfl
  | succ j ih =>
    rw [pow_succ, ih, pow_succ']
    rfl

/-- Equality of all shifted-power kernel dimensions. -/
theorem pairing_kernel_profile [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V ≃ₗ[K] V) (S : Module.End K W)
    (e : W ≃ₗ[K] Module.Dual K V) (d a : K) (hd : d ≠ 0) (ha : a ≠ 0)
    (h : ∀ x y, e (S y) (T x) = d * e y x) (j : ℕ) :
    Module.finrank K (LinearMap.ker ((S-(d/a) • 1)^j)) =
      Module.finrank K (LinearMap.ker ((T.toLinearMap-a • 1)^j)) := by
  let D := T.toLinearMap-a • 1
  let Q : Module.End K V := (-d/a) • T.symm.toLinearMap
  let E : Module.End K V := d • T.symm.toLinearMap-(d/a) • 1
  have heq : E = D*Q := by
    ext x
    dsimp [E,D,Q]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mul_apply, map_smul, T.apply_symm_apply]
    simp only [map_sub, smul_sub, smul_smul]
    rw [show a*(-d/a) = -d by field_simp]
    module
  have hcomm : Commute D Q := by
    apply Commute.smul_right
    apply Commute.sub_left
    · ext x; simp [Module.End.mul_apply]
    · exact (Commute.one_left _).smul_left a
  have hunit : IsUnit Q := by
    apply (Module.End.isUnit_iff Q).mpr
    have hc : -d/a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hd) ha
    constructor
    · intro x y hxy
      apply T.symm.injective
      have hh := congrArg (fun z : V => (-d/a)⁻¹ • z) hxy
      change (-d/a)⁻¹ • ((-d/a) • T.symm x) =
        (-d/a)⁻¹ • ((-d/a) • T.symm y) at hh
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul] at hh
      exact hh
    · intro y
      refine ⟨T ((-d/a)⁻¹ • y), ?_⟩
      change (-d/a) • T.symm (T ((-d/a)⁻¹ • y)) = y
      rw [T.symm_apply_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have he : ∀ y, e ((S-(d/a) • 1) y) = E.dualMap (e y) := by
    intro y
    ext x
    have h' := h (T.symm x) y
    simp only [T.apply_symm_apply] at h'
    simp [E, LinearMap.sub_apply, h', map_sub, map_smul, mul_comm]
  calc
    _ = Module.finrank K (LinearMap.ker ((E.dualMap)^j)) :=
      (intertwiningKerEquiv e _ _ (intertwining_pow _ _ e.toLinearMap he j)).finrank_eq
    _ = Module.finrank K (LinearMap.ker (E^j)) := by
      rw [dual_pow]; exact dual_ker_finrank _
    _ = Module.finrank K (LinearMap.ker (D^j)) := by
      rw [heq, (unit_factor_filtrations D Q hcomm hunit j).1]

end JordanSize
