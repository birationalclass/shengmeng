module
public import Linear.IntegerShiftedFreeGeneralRelationBiproduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {K S L : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

/-- The ORIGINAL integer coefficient dual comparison,assembled from the
actual original finite dual and original Submodule.pi coordinates. -/
def integerShiftedFreeDegreeCoefficientDualIso [Fintype L] [DecidableEq L]
    (w : L → ℤ) (d : ℤ) :
    (⨁ fun i => ModuleCat.of K (Module.Dual K (nativeProjectiveRingIntegerPiece B (w i+d)))) ≅
      ModuleCat.of K (Module.Dual K (integerShiftedFreeDualCoordinatePiece B w d)) :=
  (finiteBiproductDualIso
    (fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (w i+d)))).trans
      (integerShiftedFreeDualCoordinatePiEquiv B w d).dualMap.toModuleIso

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ) (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z t →
  c x ∈ integerShiftedFreePiece B w t)

/-- For EVERY ORIGINAL integer degree and weight family,the matrix of
the ACTUAL original coefficient-entry duals is ORIGINAL Delta_d*,with
original dual coordinates. No matrix comparison or finiteness of any
homogeneous piece is assumed. -/
theorem integerShiftedFreeDegreeRelationDual_matrix (d : ℤ) :
    biproduct.matrix (fun i j => ModuleCat.ofHom
      (integerShiftedFreeDualRelationEntry B z w c hc d i j).hom.dualMap) ≫
      (integerShiftedFreeDegreeCoefficientDualIso B w d).hom =
    (integerShiftedFreeDegreeCoefficientDualIso B z d).hom ≫
      ModuleCat.ofHom (integerShiftedFreeDualDegreeRelationMatrix c B z w hc d).dualMap := by
  unfold integerShiftedFreeDegreeCoefficientDualIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc,integerShiftedFreeDualRelationBiproduct_dual_matrix,Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun t => (finiteBiproductDualIso
    (fun i => ModuleCat.of K (nativeProjectiveRingIntegerPiece B (z i+d)))).hom ≫ t)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change φ (integerShiftedFreeDualCoordinatePiEquiv B z d
    (integerShiftedFreeDualDegreeRelationMatrix c B z w hc d
      ((integerShiftedFreeDualCoordinatePiEquiv B w d).symm
        (integerShiftedFreeDualCoordinatePiEquiv B w d x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end LinearStudy
