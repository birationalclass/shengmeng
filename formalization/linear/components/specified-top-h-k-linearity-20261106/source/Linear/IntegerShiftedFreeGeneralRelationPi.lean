module
public import Linear.IntegerShiftedFreeHomPiCoordinates
public import Linear.IntegerShiftedFreeGradedDualRelation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [DecidableEq I] [Fintype J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z t →
  c x ∈ integerShiftedFreePiece 𝓑 w t)

/-- The ACTUAL ORIGINAL relation Delta_d in its ORIGINAL product of
INTEGER homogeneous pieces. Every original weight and d is arbitrary;
negative pieces remain actual zero pieces. No matrix identity is an input. -/
def integerShiftedFreeDualRelationPiMap (d : ℤ) :
    (∀ j, nativeProjectiveRingIntegerPiece 𝓑 (w j+d)) →ₗ[K]
      (∀ i, nativeProjectiveRingIntegerPiece 𝓑 (z i+d)) :=
  (integerShiftedFreeDualCoordinatePiEquiv 𝓑 z d).toLinearMap.comp
    ((integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hc d).comp
      (integerShiftedFreeDualCoordinatePiEquiv 𝓑 w d).symm.toLinearMap)

/-- Original row values are ORIGINAL c(e_i)_j times original coefficient
polynomials,for EVERY original integer weight and degree. -/
theorem integerShiftedFreeDualRelationPiMap_apply (d : ℤ)
    (x : ∀ j, nativeProjectiveRingIntegerPiece 𝓑 (w j+d)) (i : I) :
    (integerShiftedFreeDualRelationPiMap 𝓑 z w c hc d x i).1 =
      ∑ j, integerShiftedFreeMapEntry c i j * (x j).1 := by
  change (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hc d
    ((integerShiftedFreeDualCoordinatePiEquiv 𝓑 w d).symm x)).1 i = _
  rw [integerShiftedFreeDualDegreeRelationMatrix_apply]
  rfl

/-- A single original integer coefficient has its ORIGINAL actual entry
product;negative zero pieces are included,not discarded. -/
theorem integerShiftedFreeDualRelationPiMap_single [DecidableEq J] (d : ℤ)
    (j : J) (i : I) (q : nativeProjectiveRingIntegerPiece 𝓑 (w j+d)) :
    (integerShiftedFreeDualRelationPiMap 𝓑 z w c hc d (Pi.single j q) i).1 =
      integerShiftedFreeMapEntry c i j * q.1 := by
  rw [integerShiftedFreeDualRelationPiMap_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

end LinearStudy
