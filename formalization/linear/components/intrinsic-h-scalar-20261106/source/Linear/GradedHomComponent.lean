module
public import Linear.GradedIntegerProjection
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [hM : SetLike.GradedSMul 𝒜 ℳ] [hN : SetLike.GradedSMul 𝒜 𝓝]

/-- The actual degree-k component of an arbitrary module map, assembled
from the actual decomposition of its input. Integer k allows negative shifts. -/
def gradedHomComponentAux (f : M →ₗ[A] N) (k : ℤ) : M →ₗ[K] N := by
  classical
  exact (DirectSum.toModule K ℕ N (fun d =>
    (gradedIntegerProjection 𝓝 ((d : ℤ)+k)).comp
      ((f.restrictScalars K).comp (ℳ d).subtype))).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem gradedHomComponentAux_on_piece (f : M →ₗ[A] N) (k : ℤ)
    (d : ℕ) (x : M) (hx : x ∈ ℳ d) :
    gradedHomComponentAux ℳ 𝓝 f k x =
      gradedIntegerProjection 𝓝 ((d : ℤ)+k) (f x) := by
  classical
  change (DirectSum.toModule K ℕ N (fun d =>
    (gradedIntegerProjection 𝓝 ((d : ℤ)+k)).comp
      ((f.restrictScalars K).comp (ℳ d).subtype)))
    (DirectSum.decomposeLinearEquiv ℳ x) = _
  rw [show DirectSum.decomposeLinearEquiv ℳ x =
    DirectSum.lof K ℕ (fun d => ℳ d) d ⟨x,hx⟩ from
      DirectSum.decomposeLinearEquiv_apply_coe ℳ d ⟨x,hx⟩]
  rw [DirectSum.toModule_lof]
  rfl

include 𝒜 hM hN in
/-- Taking the actual degree-k component preserves module linearity;
this follows from the exact projection shift, not an assumed graded Hom. -/
theorem gradedHomComponentAux_smul (f : M →ₗ[A] N) (k : ℤ) (a : A) (x : M) :
    gradedHomComponentAux ℳ 𝓝 f k (a • x) =
      a • gradedHomComponentAux ℳ 𝓝 f k x := by
  have hhom (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) (x : M) :
      gradedHomComponentAux ℳ 𝓝 f k (a • x) =
        a • gradedHomComponentAux ℳ 𝓝 f k x := by
    induction x using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous j x =>
      rw [gradedHomComponentAux_on_piece ℳ 𝓝 f k (d+j) (a • (x : M))
        (SetLike.GradedSMul.smul_mem ha x.property),
        gradedHomComponentAux_on_piece ℳ 𝓝 f k j (x : M) x.property,
        map_smul, gradedIntegerProjection_smul_homogeneous 𝒜 𝓝 d
          (((d+j : ℕ) : ℤ)+k) a ha (f x)]
      have hshift : (((d+j : ℕ) : ℤ)+k)-(d : ℤ) = (j : ℤ)+k := by omega
      rw [hshift]
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous d a => exact hhom d a a.property x
  | add a b ha hb => simp only [add_smul,map_add,ha,hb]

def gradedHomComponent (f : M →ₗ[A] N) (k : ℤ) : M →ₗ[A] N where
  toFun := gradedHomComponentAux ℳ 𝓝 f k
  map_add' := map_add (gradedHomComponentAux ℳ 𝓝 f k)
  map_smul' := gradedHomComponentAux_smul 𝒜 ℳ 𝓝 f k

end LinearStudy
