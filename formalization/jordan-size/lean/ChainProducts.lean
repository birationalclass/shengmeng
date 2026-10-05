import GeneralizedProducts
import Mathlib.LinearAlgebra.LinearIndependent.Basic

noncomputable section
namespace JordanSize
variable {K V W Z : Type*} [Field K]
 [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
 [AddCommGroup Z] [Module K Z]

/-- The highest surviving term, with lengths written as p+1 and q+1. -/
theorem product_top (B : V →ₗ[K] W →ₗ[K] Z)
    (T : Module.End K V) (S : Module.End K W) (R : Module.End K Z)
    (h : ∀ x y, R (B x y) = B (T x) (S y)) (a b : K)
    (p q : ℕ) (x : V) (y : W)
    (hx : ((T-a • 1)^(p+1)) x = 0)
    (hy : ((S-b • 1)^(q+1)) y = 0) :
    ((R-(a*b) • 1)^(p+q)) (B x y) =
      ((Nat.choose (p+q) p : K) * b^p * a^q) •
        B (((T-a • 1)^p) x) (((S-b • 1)^q) y) := by
  induction p generalizing x q y with
  | zero =>
    have hx' : (T-a • 1) x = 0 := by simpa using hx
    induction q generalizing y with
    | zero => simp
    | succ q ih =>
      have hy' : ((S-b • 1)^(q+1)) ((S-b • 1) y) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hy
      rw [Nat.zero_add, pow_succ, Module.End.mul_apply,
        shifted_product B T S R h, hx']
      simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, add_zero,
        map_smul]
      rw [show ((R-(a*b) • 1)^q) (B x ((S-b • 1) y)) = _ from by simpa only [Nat.zero_add] using ih ((S-b • 1) y) hy']
      simp [pow_succ, Module.End.mul_apply, smul_smul, mul_comm]
  | succ p ih =>
    induction q generalizing y with
    | zero =>
      have hy' : (S-b • 1) y = 0 := by simpa using hy
      have hx' : ((T-a • 1)^(p+1)) ((T-a • 1) x) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hx
      rw [Nat.add_zero, pow_succ, Module.End.mul_apply,
        shifted_product B T S R h, hy']
      simp only [map_zero, smul_zero, add_zero, map_smul]
      rw [show ((R-(a*b) • 1)^p) (B ((T-a • 1) x) y) = _ from by simpa only [Nat.add_zero] using ih 0 ((T-a • 1) x) y hx' (by simpa using hy')]
      simp [pow_succ, Module.End.mul_apply, smul_smul, mul_comm]
    | succ q jh =>
      have hx' : ((T-a • 1)^(p+1)) ((T-a • 1) x) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((S-b • 1)^(q+1)) ((S-b • 1) y) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hy
      have h1 := ih (q+1) ((T-a • 1) x) y hx' hy
      have h2 := jh ((S-b • 1) y) hy'
      have h3 := generalizedProduct B T S R h a b (p+1) (q+1)
        ((T-a • 1) x) ((S-b • 1) y) hx' hy'
      have e : p+1+(q+1) = (p+q+1)+1 := by omega
      rw [e, pow_succ, Module.End.mul_apply, shifted_product B T S R h]
      simp only [map_add, map_smul]
      simp only [show p+(q+1)=p+q+1 by omega] at h1
      simp only [show p+1+q=p+q+1 by omega] at h2
      simp only [show p+1+(q+1)-1=p+q+1 by omega] at h3
      rw [h1, h2, h3, add_zero]
      simp only [← Module.End.mul_apply, ← pow_succ, smul_smul]
      rw [← add_smul]
      congr 1
      rw [show Nat.choose (p+q+1+1) (p+1) =
        Nat.choose (p+q+1) p + Nat.choose (p+q+1) (p+1) from
        Nat.choose_succ_succ (p+q+1) p, Nat.cast_add]
      ring

end JordanSize

