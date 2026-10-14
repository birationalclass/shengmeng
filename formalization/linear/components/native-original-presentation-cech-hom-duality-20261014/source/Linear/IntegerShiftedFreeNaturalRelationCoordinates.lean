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

/-- The ACTUAL original Hom-coefficient tuple at degree -N with weights
a_j+N is the product of the ORIGINAL natural pieces. This comparison
precedes duality and preserves the underlying original polynomials. -/
def integerShiftedFreeDualNaturalCoordinatePiEquiv (N : ℕ) (a : J → ℕ) :
    integerShiftedFreeDualCoordinatePiece 𝓑
      (fun j => (a j:ℤ)+(N:ℤ)) (-(N:ℤ)) ≃ₗ[K] (∀ j, 𝓑 (a j)) :=
  (integerShiftedFreeDualCoordinatePiEquiv 𝓑 (fun j => (a j:ℤ)+(N:ℤ)) (-(N:ℤ))).trans
    (LinearEquiv.piCongrRight (fun j => LinearEquiv.ofEq _ _ (by
      simp [nativeProjectiveRingIntegerPiece])))

omit [GradedAlgebra 𝓑] in
/-- The original natural-degree coordinate is unchanged. -/
theorem integerShiftedFreeDualNaturalCoordinatePiEquiv_apply (N : ℕ) (a : J → ℕ)
    (x : integerShiftedFreeDualCoordinatePiece 𝓑 (fun j => (a j:ℤ)+(N:ℤ)) (-(N:ℤ))) (j : J) :
    (integerShiftedFreeDualNaturalCoordinatePiEquiv 𝓑 N a x j).1 = x.1 j := rfl

omit [GradedAlgebra 𝓑] in
/-- The original inverse natural-coordinate polynomial is also unchanged. -/
theorem integerShiftedFreeDualNaturalCoordinatePiEquiv_symm_apply (N : ℕ) (a : J → ℕ)
    (x : ∀ j, 𝓑 (a j)) (j : J) :
    ((integerShiftedFreeDualNaturalCoordinatePiEquiv 𝓑 N a).symm x).1 j = (x j).1 := rfl

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (N : ℕ) (a : I → ℕ) (b : J → ℕ)
variable (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ d : ℤ, ∀ x : I → S,
  x ∈ integerShiftedFreePiece 𝓑 (fun i => (a i:ℤ)+(N:ℤ)) d →
    c x ∈ integerShiftedFreePiece 𝓑 (fun j => (b j:ℤ)+(N:ℤ)) d)

/-- Put the ACTUAL ORIGINAL degree-relation map Delta_-N into its
constructed ORIGINAL product-of-pieces coordinates. No multiplication
matrix or duality identity is supplied as a premise. -/
def integerShiftedFreeNaturalDualRelationMatrix :
    (∀ j, 𝓑 (b j)) →ₗ[K] (∀ i, 𝓑 (a i)) :=
  (integerShiftedFreeDualNaturalCoordinatePiEquiv 𝓑 N a).toLinearMap.comp
    ((integerShiftedFreeDualDegreeRelationMatrix c 𝓑
      (fun i => (a i:ℤ)+(N:ℤ)) (fun j => (b j:ℤ)+(N:ℤ)) hc (-(N:ℤ))).comp
        (integerShiftedFreeDualNaturalCoordinatePiEquiv 𝓑 N b).symm.toLinearMap)

omit [Fintype I] [DecidableEq J] in
/-- Each ORIGINAL natural-degree relation row is its ACTUAL original
sum of entry products c(e_i)_j*x_j. All coordinate transport is proved. -/
theorem integerShiftedFreeNaturalDualRelationMatrix_apply
    (x : ∀ j, 𝓑 (b j)) (i : I) :
    (integerShiftedFreeNaturalDualRelationMatrix 𝓑 N a b c hc x i).1 =
      ∑ j, integerShiftedFreeMapEntry c i j * (x j).1 := by
  change (integerShiftedFreeDualDegreeRelationMatrix c 𝓑
    (fun i => (a i:ℤ)+(N:ℤ)) (fun j => (b j:ℤ)+(N:ℤ)) hc (-(N:ℤ))
      ((integerShiftedFreeDualNaturalCoordinatePiEquiv 𝓑 N b).symm x)).1 i = _
  rw [integerShiftedFreeDualDegreeRelationMatrix_apply]
  rfl

/-- A single original coordinate gives the ORIGINAL entry product.
This is the actual original relation component needed before dualizing. -/
theorem integerShiftedFreeNaturalDualRelationMatrix_single
    (j : J) (i : I) (q : 𝓑 (b j)) :
    (integerShiftedFreeNaturalDualRelationMatrix 𝓑 N a b c hc (Pi.single j q) i).1 =
      integerShiftedFreeMapEntry c i j * q.1 := by
  rw [integerShiftedFreeNaturalDualRelationMatrix_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

end LinearStudy
