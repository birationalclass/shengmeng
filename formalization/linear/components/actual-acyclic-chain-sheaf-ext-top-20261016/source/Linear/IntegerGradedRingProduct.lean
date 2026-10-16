module
public import Linear.NativeProjectiveRingIntegerPieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Multiplication in the ORIGINAL ring respects its actual integer
homogeneous pieces,including negative zero pieces. This is used to
realize the original homogeneous Hom kernel by polynomial coordinates. -/
theorem nativeProjectiveRingIntegerPiece_mul_mem {d e : ℤ} {x y : S}
    (hx : x ∈ nativeProjectiveRingIntegerPiece 𝓑 d)
    (hy : y ∈ nativeProjectiveRingIntegerPiece 𝓑 e) :
    x*y ∈ nativeProjectiveRingIntegerPiece 𝓑 (d+e) := by
  by_cases hd : 0 ≤ d
  · have hx' : x ∈ 𝓑 d.toNat := by
      unfold nativeProjectiveRingIntegerPiece at hx
      rwa [ite_eq_left hd] at hx
    have hmul := nativeProjectiveRingIntegerPiece_graded 𝓑 d.toNat e x hx' y hy
    have hdeg : (d.toNat : ℤ)+e = d+e := by omega
    simpa only [hdeg,smul_eq_mul] using hmul
  · unfold nativeProjectiveRingIntegerPiece at hx
    rw [ite_eq_right hd,Submodule.mem_bot] at hx
    subst x
    simpa only [zero_mul] using (nativeProjectiveRingIntegerPiece 𝓑 (d+e)).zero_mem

end LinearStudy
