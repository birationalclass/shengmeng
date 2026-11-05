module
public import Linear.IntegerShiftedFreeDualRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
  c x ∈ integerShiftedFreePiece B w d)

/-- Original coefficient transport in the inverse direction also keeps
every original polynomial value. -/
theorem integerShiftedFreeDualCoordinateRegradingEquiv_symm_apply (k d : ℤ)
    (x : integerShiftedFreeDualCoordinatePiece B w (d-k)) :
    ((integerShiftedFreeDualCoordinateRegradingEquiv B w k d).symm x).1=x.1 := rfl

/-- The ACTUAL original relation Delta regrades with unchanged ORIGINAL
matrix c(e_i)_j and all original tuple values,including negative pieces. -/
theorem integerShiftedFreeDualDegreeRelationMatrix_regrade (k d : ℤ)
    (x : integerShiftedFreeDualCoordinatePiece B (fun j => w j-k) d) :
    integerShiftedFreeDualCoordinateRegradingEquiv B z k d
      (integerShiftedFreeDualDegreeRelationMatrix c B (fun i => z i-k) (fun j => w j-k)
        (integerShiftedFreeRelation_regrade B z w c hc k) d x) =
    integerShiftedFreeDualDegreeRelationMatrix c B z w hc (d-k)
      (integerShiftedFreeDualCoordinateRegradingEquiv B w k d x) := by
  apply Subtype.ext
  funext i
  rfl

/-- EXACT contravariant original whole relation square for EVERY integer
regrading. Actual matrix and actual coefficient duals are used. -/
theorem integerShiftedFreeRelationDualMap_regrade (k d : ℤ) :
    ModuleCat.ofHom (integerShiftedFreeDualDegreeRelationMatrix c B
      (fun i => z i-k) (fun j => w j-k) (integerShiftedFreeRelation_regrade B z w c hc k) d).dualMap ≫
      (integerShiftedFreeDualCoordinateRegradingEquiv B w k d).dualMap.toModuleIso.inv =
    (integerShiftedFreeDualCoordinateRegradingEquiv B z k d).dualMap.toModuleIso.inv ≫
      ModuleCat.ofHom (integerShiftedFreeDualDegreeRelationMatrix c B z w hc (d-k)).dualMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply LinearMap.ext
  intro x
  change ell (integerShiftedFreeDualDegreeRelationMatrix c B
    (fun i => z i-k) (fun j => w j-k) (integerShiftedFreeRelation_regrade B z w c hc k) d
    ((integerShiftedFreeDualCoordinateRegradingEquiv B w k d).symm x)) =
      ell ((integerShiftedFreeDualCoordinateRegradingEquiv B z k d).symm
        (integerShiftedFreeDualDegreeRelationMatrix c B z w hc (d-k) x))
  congr 1

end LinearStudy
