module
public import Linear.ActualAffineAlgebraDualSpecValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Equality of actual affine internal-Hom sections is detected by
their values on the original algebra elements through the actual tilde
and structure-pushforward isomorphism. No generation certificate is assumed. -/
theorem actualAffineAlgebraDualInternalHomSections_evaluation_ext
    (h k : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤))
    (H : ∀ b : B,
      schemeModuleHomSectionEvaluation _ _ ⊤ h
        ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b)) =
      schemeModuleHomSectionEvaluation _ _ ⊤ k
        ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))) :
    h = k := by
  obtain ⟨f,rfl⟩ := (actualAffineAlgebraDualInternalHomSectionsLinearEquiv
    (A := A) (B := B)).surjective h
  obtain ⟨g,rfl⟩ := (actualAffineAlgebraDualInternalHomSectionsLinearEquiv
    (A := A) (B := B)).surjective k
  apply congrArg (actualAffineAlgebraDualInternalHomSectionsLinearEquiv
    (A := A) (B := B))
  ext b
  have hb := H b
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
    actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value] at hb
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (CommRingCat.of A)).inv).injective hb

end LinearStudy
