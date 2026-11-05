module
public import Linear.NativeProjectiveModuleSheafMap
public import Linear.GradedIntegerProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The ORIGINAL nonnegatively graded ring viewed in integer degrees;
negative pieces are zero. It is the actual ring, not a supplied twist model. -/
def nativeProjectiveRingIntegerPiece (d : ℤ) : Submodule K S :=
  if 0 ≤ d then 𝓑 d.toNat else ⊥

theorem nativeProjectiveRingIntegerPiece_graded
    (n : ℕ) (d : ℤ) (b : S) (hb : b ∈ 𝓑 n)
    (ell : S) (hell : ell ∈ nativeProjectiveRingIntegerPiece 𝓑 d) :
    b • ell ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+d) := by
  unfold nativeProjectiveRingIntegerPiece at hell ⊢
  by_cases hd : 0 ≤ d
  · have hnd : 0 ≤ (n : ℤ)+d := by omega
    rw [ite_eq_left hd] at hell
    rw [ite_eq_left hnd]
    have hcast : ((n : ℤ)+d).toNat = n+d.toNat := by omega
    rw [hcast]
    exact SetLike.mul_mem_graded hb hell
  · rw [ite_eq_right hd,Submodule.mem_bot] at hell
    subst ell
    simp

/-- A fixed point of the actual integer homogeneous projection lies
in precisely the actual integer piece, including negative degrees. -/
theorem nativeProjectiveRingIntegerPiece_mem_of_projection
    (d : ℤ) (x : S) (hx : x = gradedIntegerProjection 𝓑 d x) :
    x ∈ nativeProjectiveRingIntegerPiece 𝓑 d := by
  unfold nativeProjectiveRingIntegerPiece
  unfold gradedIntegerProjection at hx
  by_cases hd : 0 ≤ d
  · rw [ite_eq_left hd] at hx ⊢
    rw [hx]
    exact (DirectSum.decompose 𝓑 x d.toNat).property
  · rw [ite_eq_right hd] at hx ⊢
    simpa only [Submodule.mem_bot,LinearMap.zero_apply] using hx

end LinearStudy
