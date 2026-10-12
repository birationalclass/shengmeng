module
public import Linear.ActualAffineHomSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual affine comparison preserves every original source-algebra
scalar. Both sides use the original coextension and internal Hom. -/
theorem actualAffineNativeDualInternalHom_original_source_action
    (ell : (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)))
    (b : B) :
    actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B)
      (nativeCoextensionOriginalDualEquiv (R := A) (S := B) (b • ell)) =
    schemePushforwardHomSourceActionSection
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⊤
      (show Γ(Spec (CommRingCat.of B),
         Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ ⊤) from
        (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))
      (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B)
        (nativeCoextensionOriginalDualEquiv (R := A) (S := B) ell)) := by
  apply actualAffineAlgebraDualInternalHomSections_evaluation_ext
  intro x
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value]
  rw [schemePushforwardHomSourceActionSection_original_evaluation]
  rw [← actualAffineAlgebraStructurePushforwardIso_element_mul]
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
    nativeCoextensionOriginalDualEquiv_upper_smul]
  rw [mul_comm x b]

end LinearStudy
