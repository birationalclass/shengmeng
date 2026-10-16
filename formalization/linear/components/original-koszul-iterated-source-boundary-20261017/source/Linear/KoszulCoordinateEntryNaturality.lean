module
public import Linear.KoszulHomogeneousCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open Module
universe u v
variable {R : Type u} {T : Type v} [CommRing R] [CommRing T]

/-- Canonical ORIGINAL coordinate-wedge coefficients commute with an
arbitrary original ring homomorphism,by their actual determinant formula. -/
theorem koszulExteriorCoordinates_wedge_map (φ : R →+* T) (r p : ℕ)
    (v : Fin p → Fin r) (t : Set.powersetCard (Fin r) p) :
    φ (koszulExteriorCoordinates (S := R) r p
      (exteriorPower.ιMulti R p ((Pi.basisFun R (Fin r)) ∘ v)) t) =
    koszulExteriorCoordinates (S := T) r p
      (exteriorPower.ιMulti T p ((Pi.basisFun T (Fin r)) ∘ v)) t := by
  classical
  simp only [koszulExteriorCoordinates, Basis.equivFun_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti, Function.comp_apply]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]

/-- The actual ORIGINAL Koszul matrix entry is its alternating exterior
sum;this is proved from the original differential,not taken as a matrix premise. -/
theorem homogeneousKoszulCoordinateDifferential_entry_formula {r : ℕ}
    (H : Fin r → R) (p : ℕ) (s : Set.powersetCard (Fin r) (p+1))
    (t : Set.powersetCard (Fin r) p) :
    integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) s t =
      ∑ i : Fin (p+1), ((-1:R)^(i:ℕ) * H (Set.powersetCard.ofFinEmbEquiv.symm s i)) *
        koszulExteriorCoordinates (S := R) r p
          (exteriorPower.ιMulti R p ((Pi.basisFun R (Fin r)) ∘
            i.removeNth (Set.powersetCard.ofFinEmbEquiv.symm s : Fin (p+1) → Fin r))) t := by
  classical
  change koszulExteriorCoordinates (S := R) r p
    (koszulComplex.d (Fintype.linearCombination R H) p
      ((koszulExteriorCoordinates (S := R) r (p+1)).symm (Pi.single s 1))) t = _
  have hs : (koszulExteriorCoordinates (S := R) r (p+1)).symm (Pi.single s 1) =
      (Pi.basisFun R (Fin r)).exteriorPower (p+1) s := by
    apply (koszulExteriorCoordinates (S := R) r (p+1)).injective
    simp [koszulExteriorCoordinates, Basis.equivFun_self]
  rw [hs, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    koszulComplex.dAlternating_apply, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, Pi.smul_apply]
  have hlin : Fintype.linearCombination R H ((Pi.basisFun R (Fin r))
      (Set.powersetCard.ofFinEmbEquiv.symm s i)) =
        H (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
    simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  simp only [Function.comp_apply]
  rw [hlin]
  rfl

/-- EVERY actual original exterior Koszul matrix entry commutes with
an arbitrary original ring homomorphism,in the SAME canonical bases. -/
theorem homogeneousKoszulCoordinateDifferential_entry_map {r : ℕ}
    (φ : R →+* T) (H : Fin r → R) (p : ℕ)
    (s : Set.powersetCard (Fin r) (p+1)) (t : Set.powersetCard (Fin r) p) :
    φ (integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) s t) =
      integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential (φ ∘ H) p) s t := by
  rw [homogeneousKoszulCoordinateDifferential_entry_formula,
    homogeneousKoszulCoordinateDifferential_entry_formula, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, map_pow, map_neg, map_one,
    koszulExteriorCoordinates_wedge_map]
  rfl

/-- The SAME original Koszul entries are linear in the ORIGINAL forms,
with no regularity or characteristic restriction. -/
theorem homogeneousKoszulCoordinateDifferential_entry_scale {r : ℕ}
    (c : R) (H : Fin r → R) (p : ℕ)
    (s : Set.powersetCard (Fin r) (p+1)) (t : Set.powersetCard (Fin r) p) :
    integerShiftedFreeMapEntry
      (homogeneousKoszulCoordinateDifferential (fun i => c * H i) p) s t =
      c * integerShiftedFreeMapEntry (homogeneousKoszulCoordinateDifferential H p) s t := by
  rw [homogeneousKoszulCoordinateDifferential_entry_formula,
    homogeneousKoszulCoordinateDifferential_entry_formula, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end LinearStudy
