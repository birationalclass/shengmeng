module
public import Linear.IntegerShiftedFreeGeneralRelationPi
public import Linear.FiniteBiproductMatrixDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z t →
  c x ∈ integerShiftedFreePiece B w t)

/-- The ORIGINAL degree relation in the ORIGINAL finite biproduct of
INTEGER pieces. All weights and d are arbitrary. -/
def integerShiftedFreeDualRelationBiproduct (d : ℤ) :
    (⨁ fun j => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w j+d))) ⟶
      (⨁ fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d))) :=
  (ModuleCat.biproductIsoPi (fun j => ModuleCat.of K
    (nativeProjectiveRingIntegerPiece B (w j+d)))).hom ≫
  ModuleCat.ofHom (integerShiftedFreeDualRelationPiMap B z w c hc d) ≫
  (ModuleCat.biproductIsoPi (fun i => ModuleCat.of K
    (nativeProjectiveRingIntegerPiece B (z i+d)))).inv

/-- The ACTUAL relation,not a chosen abstract map,has its original
integer coefficient coordinates. -/
theorem integerShiftedFreeDualRelationBiproduct_coordinates (d : ℤ) :
    finiteBiproductMapCoordinates
      (fun j => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w j+d)))
      (fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d)))
      (integerShiftedFreeDualRelationBiproduct B z w c hc d) =
        integerShiftedFreeDualRelationPiMap B z w c hc d := by
  unfold finiteBiproductMapCoordinates integerShiftedFreeDualRelationBiproduct
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.id_comp,
    Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id]
  rfl

/-- Actual ORIGINAL categorical coefficient entry,with original zero
pieces retained. No entry comparison or duality is an input. -/
def integerShiftedFreeDualRelationEntry (d : ℤ) (i : I) (j : J) :
    ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w j+d)) ⟶
      ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d)) :=
  biproduct.components (integerShiftedFreeDualRelationBiproduct B z w c hc d) j i

/-- The actual original entry is ORIGINAL polynomial multiplication. -/
theorem integerShiftedFreeDualRelationEntry_value (d : ℤ) (i : I) (j : J)
    (q : nativeProjectiveRingIntegerPiece B (w j+d)) :
    (integerShiftedFreeDualRelationEntry B z w c hc d i j q).1 =
      integerShiftedFreeMapEntry c i j*q.1 := by
  rw [integerShiftedFreeDualRelationEntry,← finiteBiproductMapCoordinates_single,
    integerShiftedFreeDualRelationBiproduct_coordinates]
  exact integerShiftedFreeDualRelationPiMap_single B z w c hc d j i q

/-- The ORIGINAL relation transpose is the matrix of the duals of its
ACTUAL ORIGINAL entries,for every integer weight and degree. -/
theorem integerShiftedFreeDualRelationBiproduct_dual_matrix (d : ℤ) :
    biproduct.matrix (fun i j => ModuleCat.ofHom
      (integerShiftedFreeDualRelationEntry B z w c hc d i j).hom.dualMap) ≫
        (finiteBiproductDualIso
          (fun j => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w j+d)))).hom =
    (finiteBiproductDualIso
      (fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d)))).hom ≫
        ModuleCat.ofHom (integerShiftedFreeDualRelationPiMap B z w c hc d).dualMap := by
  have h := finiteBiproductActualMap_dual_matrix
    (fun j => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w j+d)))
    (fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d)))
    (integerShiftedFreeDualRelationBiproduct B z w c hc d)
  rw [integerShiftedFreeDualRelationBiproduct_coordinates] at h
  exact h

end LinearStudy
