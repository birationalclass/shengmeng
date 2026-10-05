import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic

noncomputable section
namespace JordanSize
variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z]

lemma shifted_product (B : V →ₗ[K] W →ₗ[K] Z)
    (T : Module.End K V) (S : Module.End K W) (R : Module.End K Z)
    (h : ∀ x y, R (B x y) = B (T x) (S y)) (a b : K) (x : V) (y : W) :
    (R - (a*b) • 1) (B x y) =
      b • B ((T-a • 1) x) y + a • B x ((S-b • 1) y) +
        B ((T-a • 1) x) ((S-b • 1) y) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, h]
  module

/-- A product of generalized eigenvectors has the sum-minus-one bound. -/
theorem generalizedProduct (B : V →ₗ[K] W →ₗ[K] Z)
    (T : Module.End K V) (S : Module.End K W) (R : Module.End K Z)
    (h : ∀ x y, R (B x y) = B (T x) (S y)) (a b : K)
    (p q : ℕ) (x : V) (y : W)
    (hx : ((T-a • 1)^p) x = 0) (hy : ((S-b • 1)^q) y = 0) :
    ((R-(a*b) • 1)^(p+q-1)) (B x y) = 0 := by
  induction p generalizing x q y with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ p ih =>
    induction q generalizing y with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ q jh =>
      have hx' : ((T-a • 1)^p) ((T-a • 1) x) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hx
      have hy' : ((S-b • 1)^q) ((S-b • 1) y) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hy
      have h1 := ih (q+1) ((T-a • 1) x) y hx' hy
      have h2 := jh ((S-b • 1) y) hy'
      have h3 := ih q ((T-a • 1) x) ((S-b • 1) y) hx' hy'
      have h3' : ((R-(a*b) • 1)^(p+q))
          (B ((T-a • 1) x) ((S-b • 1) y)) = 0 := by
        have he3 : p+q = (p+q-(p+q-1))+(p+q-1) := by omega
        rw [he3, pow_add, Module.End.mul_apply, h3, map_zero]
      have he : p+1+(q+1)-1 = (p+q)+1 := by omega
      rw [he, pow_succ, Module.End.mul_apply, shifted_product B T S R h]
      simp only [map_add, map_smul]
      simp only [show p+(q+1)-1=p+q by omega] at h1
      simp only [show p+1+q-1=p+q by omega] at h2
      rw [h1,h2,h3',smul_zero,smul_zero,add_zero,add_zero]

end JordanSize
#print axioms JordanSize.generalizedProduct
