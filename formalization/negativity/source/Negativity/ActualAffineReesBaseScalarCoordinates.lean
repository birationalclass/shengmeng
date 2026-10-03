module
public import Negativity.ActualAffineReesImageCoordinates

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Ambient pullback coordinates respect the genuine projection to the
base Rees spectrum, including its actual global-section coordinates. -/
theorem actual_affine_rees_section_coordinates_base_scalars (I : Ideal R) :
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I)).appTop ≫
        (actualAffineReesSectionCoordinates (S := S) I).hom =
      (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : reesAlgebra I →+* S ⊗[R] reesAlgebra I) := by
  simp only [actualAffineReesSectionCoordinates, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop]
  rw [actualAffineReesCoordinates, pullbackSpecIso_inv_snd, Scheme.ΓSpecIso_naturality]
  rfl

/-- Genuine base Rees scalars become the genuine coefficientwise Rees
base-change map in the closed-image coordinate ring. -/
theorem actual_affine_rees_image_sections_base_scalars (I : Ideal R)
    (p : reesAlgebra I) :
    actualAffineReesImageSectionsEquiv (S := S) I
      (((actualAffineReesMap (S := S) I).ker.subschemeι ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (actualReesProjection I)).appTop
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)) =
      actualReesCoefficientMap (S := S) I p := by
  have hc := ConcreteCategory.congr_hom
    (actual_affine_rees_section_coordinates_base_scalars (S := S) I)
      ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)
  change (actualAffineReesSectionCoordinates (S := S) I).hom
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (actualReesProjection I)).appTop
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)) =
    (Algebra.TensorProduct.includeRight : reesAlgebra I →ₐ[R] S ⊗[R] reesAlgebra I)
      ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)) at hc
  rw [(Scheme.ΓSpecIso (.of (reesAlgebra I))).inv_hom_id_apply] at hc
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    actual_affine_rees_image_sections_equiv_inclusion]
  change actualReesBaseChangeMap I
    ((actualAffineReesSectionCoordinates (S := S) I).hom
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (actualReesProjection I)).appTop
        ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p))) = _
  rw [hc]
  simp [actualReesBaseChangeMap, actualReesCoefficientMap]

#print axioms actual_affine_rees_section_coordinates_base_scalars
#print axioms actual_affine_rees_image_sections_base_scalars
end
end Negativity

