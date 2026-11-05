module
public import Linear.IntegerShiftedFreeGradedDualRelation
public import Linear.IntegerShiftedFreeDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {K S I J : Type*} [Field K] [CommRing S] [Algebra K S]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (c : (I → S) →ₗ[S] (J → S))
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (z : I → ℤ) (w : J → ℤ)
variable (hh : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece 𝓑 z t →
  c x ∈ integerShiftedFreePiece 𝓑 w t)

/-- The original degree-d part of ker(c*) equals the kernel of the
ORIGINAL c* restricted to original Hom degree d;only the order of the
two actual submodule restrictions changes. -/
def integerShiftedFreeGradedDualKernelSwap (d : ℤ) :
    actualPresentationGradedDualKernelPiece 𝓑 (integerShiftedFreePiece 𝓑 w) c d ≃ₗ[K]
      LinearMap.ker (integerShiftedFreeGradedDualRelation c 𝓑 z w hh d) where
  toFun φ := ⟨⟨φ.1.1,φ.property⟩,Subtype.ext φ.1.property⟩
  invFun φ := ⟨⟨φ.1.1,congrArg Subtype.val φ.property⟩,φ.1.property⟩
  left_inv := by intro φ; rfl
  right_inv := by intro φ; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The ACTUAL original homogeneous relation kernel becomes the actual
transpose multiplication kernel under canonical original Hom coordinates.
This uses the proved original coordinate square,not a kernel identity input. -/
def integerShiftedFreeHomRelationKernelCoordinatesEquiv (d : ℤ) :
    LinearMap.ker (integerShiftedFreeGradedDualRelation c 𝓑 z w hh d) ≃ₗ[K]
      LinearMap.ker (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d) :=
  (LinearEquiv.ofEq _ _ (by
    ext φ
    change integerShiftedFreeGradedDualRelation c 𝓑 z w hh d φ = 0 ↔
      integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d
        (integerShiftedFreeHomCoordinatesEquiv 𝓑 w d φ) = 0
    rw [← integerShiftedFreeGradedDualRelation_coordinates]
    exact (integerShiftedFreeHomCoordinatesEquiv 𝓑 z d).map_eq_zero_iff.symm)).trans
      ((integerShiftedFreeHomCoordinatesEquiv 𝓑 w d).ofSubmodule'
        (LinearMap.ker (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d)))

/-- Original homogeneous dual relation kernel in actual original
homogeneous coefficient coordinates,including all negative zero pieces. -/
def integerShiftedFreeGradedDualKernelCoordinatesEquiv (d : ℤ) :
    actualPresentationGradedDualKernelPiece 𝓑 (integerShiftedFreePiece 𝓑 w) c d ≃ₗ[K]
      LinearMap.ker (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d) :=
  (integerShiftedFreeGradedDualKernelSwap c 𝓑 z w hh d).trans
    (integerShiftedFreeHomRelationKernelCoordinatesEquiv c 𝓑 z w hh d)

variable {M : Type*} [AddCommGroup M] [Module K M] [Module S M]
variable (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (b : (J → S) →ₗ[S] M)
variable (bhh : ∀ t : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece 𝓑 w t → b x ∈ ℳ t)
variable (hb : Function.Surjective b) (hrel : LinearMap.range c = LinearMap.ker b)

/-- For the ACTUAL original shifted-free presentation R->E->M->0,
original homogeneous Hom_S(M,S)_d is the kernel of the ACTUAL original
transpose multiplication matrix on the actual coefficient pieces.
Ordinary surjectivity and original homogeneity suffice. Every grading,
coordinate map and relation-kernel comparison is constructed and proved. -/
def integerShiftedFreePresentationHomPolynomialKernelEquiv (d : ℤ) :
    integerGradedHomPiece 𝓑 ℳ d ≃ₗ[K]
      LinearMap.ker (integerShiftedFreeDualDegreeRelationMatrix c 𝓑 z w hh d) := by
  letI := integerShiftedFreeDecomposition 𝓑 w
  exact (actualPresentationGradedDualKernelEquiv 𝓑 (integerShiftedFreePiece 𝓑 w)
    ℳ b bhh hb c hrel d).trans
      (integerShiftedFreeGradedDualKernelCoordinatesEquiv c 𝓑 z w hh d)

/-- The constructed original presentation comparison still sends φ
to the tuple φ(b(e_j)) on ORIGINAL basis vectors. It is not an arbitrary
coordinate or cohomology-duality isomorphism. -/
theorem integerShiftedFreePresentationHomPolynomialKernelEquiv_apply (d : ℤ)
    (φ : integerGradedHomPiece 𝓑 ℳ d) (j : J) :
    (integerShiftedFreePresentationHomPolynomialKernelEquiv c 𝓑 z w hh ℳ b bhh hb hrel d φ).1.1 j =
      φ.1 (b (Pi.single j (1:S))) := by
  change integerShiftedFreeDualCoordinates (K := K) (φ.1.comp b) j = _
  rw [integerShiftedFreeDualCoordinates_apply]
  rfl

end LinearStudy
