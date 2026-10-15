module
public import Linear.Vendor.KoszulComplex
public import Linear.IntegerShiftedFreeMatrix
public import Linear.IntegerGradedRingProduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped BigOperators
open Module
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (r : ℕ)

/-- The canonical exterior basis of the ORIGINAL finite free Koszul term. -/
def koszulExteriorCoordinates (p : ℕ) :
    (⋀[S]^p (Fin r → S)) ≃ₗ[S] (Set.powersetCard (Fin r) p → S) :=
  ((Pi.basisFun S (Fin r)).exteriorPower p).equivFun

/-- A wedge of ORIGINAL coordinate vectors has degree-zero coefficients.
The coordinates are the ORIGINAL exterior-basis determinant, over K. -/
theorem koszulExteriorCoordinates_wedge_mem_zero (p : ℕ)
    (v : Fin p → Fin r) (t : Set.powersetCard (Fin r) p) :
    koszulExteriorCoordinates (S := S) r p
      (exteriorPower.ιMulti S p ((Pi.basisFun S (Fin r)) ∘ v)) t ∈ 𝓑 0 := by
  classical
  rw [koszulExteriorCoordinates, Basis.equivFun_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  let T : Matrix (Fin p) (Fin p) K := fun i j =>
    if Set.powersetCard.ofFinEmbEquiv.symm t j = v i then 1 else 0
  have hT : (Matrix.of fun i j => (Pi.basisFun S (Fin r)).coord
      (Set.powersetCard.ofFinEmbEquiv.symm t j) ((Pi.basisFun S (Fin r)) (v i))) =
        T.map (algebraMap K S) := by
    ext i j
    simp [T, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  simp only [Function.comp_apply]
  rw [hT]
  change ((algebraMap K S).mapMatrix T).det ∈ 𝓑 0
  rw [← RingHom.map_det]
  simpa only [Algebra.smul_def, mul_one] using
    (𝓑 0).smul_mem T.det (SetLike.one_mem_graded 𝓑)

/-- ORIGINAL exterior Koszul differential in its canonical coordinates.
This is defined from the original differential, not from a desired matrix. -/
def homogeneousKoszulCoordinateDifferential {r : ℕ} (H : Fin r → S) (p : ℕ) :
    (Set.powersetCard (Fin r) (p+1) → S) →ₗ[S]
      (Set.powersetCard (Fin r) p → S) :=
  (koszulExteriorCoordinates (S := S) r p).toLinearMap.comp
    ((koszulComplex.d (Fintype.linearCombination S H) p).comp
      (koszulExteriorCoordinates (S := S) r (p+1)).symm.toLinearMap)

/-- Every actual entry of the ORIGINAL differential has degree q,
derived from the original H_i and the exterior alternating-sum formula. -/
theorem homogeneousKoszulCoordinateDifferential_entry_mem {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ)
    (s : Set.powersetCard (Fin r) (p+1)) (t : Set.powersetCard (Fin r) p) :
    integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) s t ∈
      𝓑 q := by
  classical
  change koszulExteriorCoordinates (S := S) r p
    (koszulComplex.d (Fintype.linearCombination S H) p
      ((koszulExteriorCoordinates (S := S) r (p+1)).symm (Pi.single s 1))) t ∈ _
  have hsingle : (koszulExteriorCoordinates (S := S) r (p+1)).symm (Pi.single s 1) =
      (Pi.basisFun S (Fin r)).exteriorPower (p+1) s := by
    apply (koszulExteriorCoordinates (S := S) r (p+1)).injective
    simp [koszulExteriorCoordinates, Basis.equivFun_self]
  rw [hsingle, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    koszulComplex.dAlternating_apply, map_sum, Finset.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  simp only [map_smul, Pi.smul_apply]
  let v := (Set.powersetCard.ofFinEmbEquiv.symm s : Fin (p+1) → Fin r)
  have hcoeff : koszulExteriorCoordinates (S := S) r p
      (exteriorPower.ιMulti S p (i.removeNth ((Pi.basisFun S (Fin r)) ∘ v))) t ∈ 𝓑 0 := by
    have hv : i.removeNth ((Pi.basisFun S (Fin r)) ∘ v) =
        (Pi.basisFun S (Fin r)) ∘ i.removeNth v := by rfl
    rw [hv]
    exact koszulExteriorCoordinates_wedge_mem_zero 𝓑 r p (i.removeNth v) t
  have hmul := SetLike.mul_mem_graded (hH (v i)) hcoeff
  simp only [Nat.add_zero] at hmul
  have hlin : Fintype.linearCombination S H ((Pi.basisFun S (Fin r)) (v i)) = H (v i) := by
    simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  change ((-1:S) ^ (i:ℕ) * Fintype.linearCombination S H
      ((Pi.basisFun S (Fin r)) (v i))) * _ ∈ _
  rw [hlin]
  simpa only [Algebra.smul_def, map_pow, map_neg, map_one, mul_assoc] using
    (𝓑 q).smul_mem ((-1:K) ^ (i:ℕ)) hmul

/-- ORIGINAL weighted term has generator degree p*q. Its ORIGINAL
Koszul differential is degree zero, for every integer section degree. -/
theorem homogeneousKoszulCoordinateDifferential_homogeneous {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (d : ℤ)
    (x : Set.powersetCard (Fin r) (p+1) → S)
    (hx : x ∈ integerShiftedFreePiece 𝓑 (fun _ => ((p+1:ℕ):ℤ)*(q:ℤ)) d) :
    homogeneousKoszulCoordinateDifferential H p x ∈
      integerShiftedFreePiece 𝓑 (fun _ => (p:ℤ)*(q:ℤ)) d := by
  classical
  intro t ht
  rw [integerShiftedFreeMap_apply (homogeneousKoszulCoordinateDifferential H p) x t]
  apply Submodule.sum_mem
  intro s hs
  have hentry : integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) s t ∈
      nativeProjectiveRingIntegerPiece 𝓑 (q:ℤ) := by
    simpa [nativeProjectiveRingIntegerPiece] using
      homogeneousKoszulCoordinateDifferential_entry_mem 𝓑 H hH p s t
  have hm := nativeProjectiveRingIntegerPiece_mul_mem 𝓑 (hx s (Set.mem_univ s)) hentry
  have hd : d - ((p+1:ℕ):ℤ)*(q:ℤ) + (q:ℤ) = d-(p:ℤ)*(q:ℤ) := by push_cast; ring
  simpa only [hd] using hm

/-- The same ORIGINAL coordinate differential squares to zero, by the
original exterior Koszul identity and the canonical inverse coordinates. -/
theorem homogeneousKoszulCoordinateDifferential_comp {r : ℕ} (H : Fin r → S) (p : ℕ) :
    (homogeneousKoszulCoordinateDifferential H p).comp
      (homogeneousKoszulCoordinateDifferential H (p+1)) = 0 := by
  apply LinearMap.ext
  intro x
  change koszulExteriorCoordinates (S := S) r p
    (koszulComplex.d (Fintype.linearCombination S H) p
      ((koszulExteriorCoordinates (S := S) r (p+1)).symm
        (koszulExteriorCoordinates (S := S) r (p+1)
          (koszulComplex.d (Fintype.linearCombination S H) (p+1)
            ((koszulExteriorCoordinates (S := S) r (p+1+1)).symm x))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hz := LinearMap.congr_fun (koszulComplex.d_comp_eq_zero
    (Fintype.linearCombination S H) p)
    ((koszulExteriorCoordinates (S := S) r (p+1+1)).symm x)
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    congrArg (koszulExteriorCoordinates (S := S) r p) hz

end LinearStudy
