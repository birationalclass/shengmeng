module
public import Linear.CoextensionEvaluationAtOne
public import Linear.IntegerShiftedFreePieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module R M] [Module S M] [Module K M]
variable [IsScalarTower R S M]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- Reuse mathlib's ACTUAL restriction/coextension adjunction on the
ORIGINAL R-linear functional. Only the original restricted scalar action
is calibrated;the adjunction itself is not rebuilt. -/
def coextensionOriginalAdjoint (phi : Module.Dual R M) :
    M →ₗ[S] ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  let g : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ⟶
      ModuleCat.of R R := ModuleCat.ofHom
    (X:=(ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M))
    (Y:=ModuleCat.of R R) {
    toFun := fun x => phi x
    map_add' := phi.map_add
    map_smul' := by
      intro r x
      let y : M := x
      change phi (algebraMap R S r • y) = r • phi y
      rw [IsScalarTower.algebraMap_smul]
      exact phi.map_smul r x }
  exact (ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction
    (algebraMap R S) g).hom
/-- Preserve the ORIGINAL adjunction value phi(s•x),for every s. -/
theorem coextensionOriginalAdjoint_apply (phi : Module.Dual R M) (x : M) (s : S) :
    coextensionOriginalAdjoint phi x s = phi (s • x) := by
  rfl
/-- The SAME evaluation at ONE recovers the ORIGINAL R-functional. -/
theorem coextensionOriginalEvaluationAtOne_adjoint (phi : Module.Dual R M) (x : M) :
    coextensionOriginalEvaluationAtOne (R:=R) (S:=S)
      (coextensionOriginalAdjoint phi x) = phi x := by
  change phi ((1:S) • x) = phi x
  rw [one_smul]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M)
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ s : S,s ∈ B n →
  ∀ x : M,x ∈ D j → s • x ∈ D ((n:ℤ)+j))
include hS in
/-- For EVERY integer degree d,the ORIGINAL adjunction sends a degree-d
R-functional to an ORIGINAL S-linear map into the SAME coextension,
shifting homogeneous degree j to j+d. No desired homogeneity is assumed. -/
theorem coextensionOriginalAdjoint_homogeneous (d : ℤ)
    (phi : integerGradedHomPiece A D d) (j : ℤ) (x : M) (hx : x ∈ D j) :
    coextensionOriginalAdjoint phi.1 x ∈ coextensionGradedPiece A B (j+d) := by
  rw [coextensionGradedPiece_mem_iff]
  intro n s hs
  rw [coextensionOriginalAdjoint_apply]
  have hv := phi.property ((n:ℤ)+j) (s • x) (hS n j s hs x hx)
  have hp := gradedIntegerProjection_on_integerPiece A (((n:ℤ)+j)+d)
    (((n:ℤ)+j)+d) (phi.1 (s • x)) hv
  simpa only [add_assoc,ite_true] using hp.symm
end LinearStudy
