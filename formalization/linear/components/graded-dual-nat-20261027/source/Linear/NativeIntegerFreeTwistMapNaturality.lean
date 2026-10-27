module
public import Linear.NativeIntegerFreeTwistRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S I J : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → S) →ₗ[S] (J → S))
variable (hc : ∀ d : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B z d →
  c x ∈ integerShiftedFreePiece B w d)

/-- EVERY original homogeneous free-family map commutes with the ACTUAL
native free twist transports. Actual prime-localized values are retained;
no cohomology or duality map identity is an assumed premise. -/
theorem nativeIntegerFreeTwistRegradingIso_map (k : ℤ) :
    (nativeIntegerFreeTwistRegradingIso B z k).inv ≫
      nativeProjectiveDegreeZeroSheafMap B
        (integerShiftedFreePiece B (fun i => z i-k))
        (integerShiftedFreePiece B (fun j => w j-k))
        (integerShiftedFreePiece_smul_homogeneous B (fun i => z i-k))
        (integerShiftedFreePiece_smul_homogeneous B (fun j => w j-k)) c
        (integerShiftedFreeRelation_regrade B z w c hc k) 0 ≫
      (nativeIntegerFreeTwistRegradingIso B w k).hom =
    nativeProjectiveDegreeZeroSheafMap B (integerShiftedFreePiece B z)
      (integerShiftedFreePiece B w) (integerShiftedFreePiece_smul_homogeneous B z)
      (integerShiftedFreePiece_smul_homogeneous B w) c hc k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

end LinearStudy
