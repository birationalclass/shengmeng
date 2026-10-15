module
public import Linear.KoszulCoordinateEntryNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u v
variable {R : Type u} {T : Type v} [CommRing R] [CommRing T]

/-- The WHOLE SAME original standard coordinate Koszul differential
commutes with any original ring homomorphism,not only its entries. -/
theorem homogeneousKoszulCoordinateDifferential_map {r : ℕ}
    (φ : R →+* T) (H : Fin r → R) (p : ℕ)
    (x : Set.powersetCard (Fin r) (p+1) → R) :
    (fun t => φ (homogeneousKoszulCoordinateDifferential H p x t)) =
      homogeneousKoszulCoordinateDifferential (φ ∘ H) p (φ ∘ x) := by
  classical
  funext t
  rw [integerShiftedFreeMap_apply, integerShiftedFreeMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, homogeneousKoszulCoordinateDifferential_entry_map]
  rfl

end LinearStudy
