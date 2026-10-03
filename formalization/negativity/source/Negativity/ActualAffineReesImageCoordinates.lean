module

public import Negativity.ActualAffineReesMapCoordinates
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

abbrev actualAffineReesMap (I : Ideal R) :=
  actualPolynomialReesMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) I

abbrev actualAffineReesSectionCoordinates (I : Ideal R) :
    Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I), ⊤) ≅ CommRingCat.of (S ⊗[R] reesAlgebra I) :=
  asIso (actualAffineReesCoordinates (S := S) I).inv.appTop ≪≫
    Scheme.ΓSpecIso _

abbrev actualAffinePolynomialSectionCoordinates :
    Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualPolynomialProjection (R := R)), ⊤) ≅ CommRingCat.of S[X] :=
  asIso (actualAffinePolynomialCoordinates (R := R) (S := S)).inv.appTop ≪≫
    Scheme.ΓSpecIso _

/-- The actual map on global sections is the tensor-to-polynomial coordinate map. -/
theorem actual_affine_rees_sections_square (I : Ideal R) :
    (actualAffineReesMap (S := S) I).appTop ≫
        (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).hom =
      (actualAffineReesSectionCoordinates (S := S) I).hom ≫
        CommRingCat.ofHom (actualReesPolynomialMap (S := S) I).toRingHom := by
  have hf : actualAffineReesMap (S := S) I =
      (actualAffinePolynomialCoordinates (R := R) (S := S)).hom ≫
        Spec.map (CommRingCat.ofHom (actualReesPolynomialMap (S := S) I).toRingHom) ≫
        (actualAffineReesCoordinates (S := S) I).inv := by
    apply (cancel_mono (actualAffineReesCoordinates (S := S) I).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      actual_affine_polynomial_rees_map_coordinates (S := S) I
  have hx : (actualAffinePolynomialCoordinates (R := R) (S := S)).hom.appTop ≫
      (actualAffinePolynomialCoordinates (R := R) (S := S)).inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  rw [hf]
  simp only [actualAffinePolynomialSectionCoordinates, actualAffineReesSectionCoordinates,
    Iso.trans_hom, asIso_hom, Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Category.assoc (actualAffinePolynomialCoordinates (R := R) (S := S)).hom.appTop,
    hx, Category.id_comp]
  simp only [Scheme.ΓSpecIso_naturality]

/-- Pull a genuine ambient Rees-base-change section into the image Rees algebra. -/
def actualAffineReesImageSectionMap (I : Ideal R) :
    Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I), ⊤) →+* reesAlgebra (I.map (algebraMap R S)) :=
  (actualReesBaseChangeMap (S := S) I).toRingHom.comp
    (actualAffineReesSectionCoordinates (S := S) I).hom.hom

theorem actual_affine_rees_image_section_map_surjective (I : Ideal R) :
    Function.Surjective (actualAffineReesImageSectionMap (S := S) I) :=
  (actual_rees_base_change_surjective (S := S) I).comp
    (actualAffineReesSectionCoordinates (S := S) I).commRingCatIsoToRingEquiv.surjective

theorem actual_affine_rees_image_section_map_kernel (I : Ideal R) :
    RingHom.ker (actualAffineReesImageSectionMap (S := S) I) =
      RingHom.ker (actualAffineReesMap (S := S) I).appTop.hom := by
  ext x
  change actualAffineReesImageSectionMap I x = 0 ↔ (actualAffineReesMap I).appTop x = 0
  have he := ConcreteCategory.congr_hom (actual_affine_rees_sections_square (S := S) I) x
  change (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).hom
      ((actualAffineReesMap I).appTop x) = (actualAffineReesImageSectionMap I x).1 at he
  constructor
  · intro hx
    apply (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).commRingCatIsoToRingEquiv.injective
    change (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).hom
        ((actualAffineReesMap I).appTop x) =
      (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).hom 0
    rw [he, hx]
    simp
  · intro hx
    apply Subtype.ext
    rw [← he, hx]
    simp

local instance actualAffineReesPullbackIsAffine (I : Ideal R) :
    IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I)) :=
  IsAffine.of_isIso (actualAffineReesCoordinates (S := S) I).hom

/-- Sections of the actual closed image are the quotient by the actual morphism kernel. -/
def actualAffineReesImageQuotientSections (I : Ideal R) :
    Γ(actualRelativeReesScheme (Spec.map (CommRingCat.ofHom (algebraMap R S))) I, ⊤) ≅
      CommRingCat.of (Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (actualReesProjection I), ⊤) ⧸
          (actualAffineReesMap (S := S) I).ker.ideal ⟨⊤, isAffineOpen_top _⟩) := by
  simpa only [actualRelativeReesScheme, actualAffineReesMap, TopologicalSpace.Opens.map_top] using
    (actualAffineReesMap (S := S) I).ker.subschemeObjIso ⟨⊤, isAffineOpen_top _⟩

local instance actualAffineReesMapIsAffine (I : Ideal R) :
    IsAffineHom (actualAffineReesMap (S := S) I) :=
  actual_polynomial_rees_map_affine _ I

theorem actual_affine_rees_kernel_top (I : Ideal R) :
    (actualAffineReesMap (S := S) I).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      RingHom.ker (actualAffineReesImageSectionMap (S := S) I) := by
  rw [Scheme.Hom.ker_apply, actual_affine_rees_image_section_map_kernel]

/-- The genuine closed image has precisely the Rees algebra of the extended ideal as global sections.
No flatness, characteristic or finite-generation assumption is required. -/
def actualAffineReesImageSectionsEquiv (I : Ideal R) :
    Γ(actualRelativeReesScheme (Spec.map (CommRingCat.ofHom (algebraMap R S))) I, ⊤) ≃+*
      reesAlgebra (I.map (algebraMap R S)) :=
  (actualAffineReesImageQuotientSections (S := S) I).commRingCatIsoToRingEquiv.trans
    ((Ideal.quotEquivOfEq (actual_affine_rees_kernel_top (S := S) I)).trans
      (RingHom.quotientKerEquivOfSurjective
        (actual_affine_rees_image_section_map_surjective (S := S) I)))

/-- The image coordinate equivalence carries the actual closed immersion section map to the
surjective tensor-to-image Rees map. -/
theorem actual_affine_rees_image_sections_equiv_inclusion (I : Ideal R)
    (x : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I), ⊤)) :
    actualAffineReesImageSectionsEquiv (S := S) I
        ((actualAffineReesMap (S := S) I).ker.subschemeι.appTop x) =
      actualAffineReesImageSectionMap (S := S) I x := by
  have hq : (actualAffineReesImageQuotientSections (S := S) I).commRingCatIsoToRingEquiv
      ((actualAffineReesMap (S := S) I).ker.subschemeι.appTop x) =
        Ideal.Quotient.mk _ x := by
    change ((actualAffineReesMap (S := S) I).ker.subschemeObjIso
      ⟨⊤, isAffineOpen_top _⟩).hom
        ((actualAffineReesMap (S := S) I).ker.subschemeι.app ⊤ x) = _
    rw [(actualAffineReesMap (S := S) I).ker.subschemeι_app ⟨⊤, isAffineOpen_top _⟩]
    simp
  simp only [actualAffineReesImageSectionsEquiv, RingEquiv.trans_apply, hq,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The inverse image-coordinate map sends the actual tensor image back to its genuine
closed-image section. -/
theorem actual_affine_rees_image_sections_equiv_symm_map (I : Ideal R)
    (x : Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I), ⊤)) :
    (actualAffineReesImageSectionsEquiv (S := S) I).symm
        (actualAffineReesImageSectionMap (S := S) I x) =
      (actualAffineReesMap (S := S) I).ker.subschemeι.appTop x := by
  apply (actualAffineReesImageSectionsEquiv (S := S) I).injective
  simp only [RingEquiv.apply_symm_apply, actual_affine_rees_image_sections_equiv_inclusion]

/-- The actual factor map to the image is its coordinate-algebra inclusion into S[t]. -/
theorem actual_affine_rees_image_sections_equiv_factor (I : Ideal R)
    (y : Γ(actualRelativeReesScheme (Spec.map (CommRingCat.ofHom (algebraMap R S))) I, ⊤)) :
    (actualAffinePolynomialSectionCoordinates (R := R) (S := S)).hom
        ((actualAffineReesMap (S := S) I).toImage.appTop y) =
      (actualAffineReesImageSectionsEquiv (S := S) I y).1 := by
  obtain ⟨x, hx⟩ := (actualAffineReesMap (S := S) I).ker.subschemeι_app_surjective
    ⟨⊤, isAffineOpen_top _⟩ y
  change (actualAffineReesMap (S := S) I).ker.subschemeι.appTop x = y at hx
  rw [← hx, actual_affine_rees_image_sections_equiv_inclusion]
  have hi : (actualAffineReesMap (S := S) I).toImage.appTop
      ((actualAffineReesMap (S := S) I).ker.subschemeι.appTop x) =
        (actualAffineReesMap (S := S) I).appTop x := by
    have h := congrArg Scheme.Hom.appTop (actualAffineReesMap (S := S) I).toImage_imageι
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      ConcreteCategory.congr_hom h x
  rw [hi]
  exact ConcreteCategory.congr_hom (actual_affine_rees_sections_square (S := S) I) x

/-- Pure tensors have the expected image coordinates, with no flatness assumption. -/
theorem actual_affine_rees_image_sections_on_tensors (I : Ideal R) (s : S) (p : reesAlgebra I) :
    (actualAffineReesImageSectionsEquiv (S := S) I
      ((actualAffineReesMap (S := S) I).ker.subschemeι.appTop
        ((actualAffineReesSectionCoordinates (S := S) I).inv (s ⊗ₜ[R] p)))).1 =
      s • p.1.map (algebraMap R S) := by
  rw [actual_affine_rees_image_sections_equiv_inclusion]
  change (actualReesBaseChangeMap I
    ((actualAffineReesSectionCoordinates (S := S) I).hom
      ((actualAffineReesSectionCoordinates (S := S) I).inv (s ⊗ₜ[R] p)))).1 = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  simp [actualReesBaseChangeMap, actualReesCoefficientMap]

/-- The ambient coordinate identification respects the actual projection to Spec S. -/
theorem actual_affine_rees_section_coordinates_coefficients (I : Ideal R) :
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (actualReesProjection I)).appTop ≫
        (actualAffineReesSectionCoordinates (S := S) I).hom =
      (Scheme.ΓSpecIso (.of S)).hom ≫
        CommRingCat.ofHom (algebraMap S (S ⊗[R] reesAlgebra I)) := by
  simp only [actualAffineReesSectionCoordinates, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop]
  rw [actualAffineReesCoordinates, pullbackSpecIso_inv_fst, Scheme.ΓSpecIso_naturality]
  rfl

/-- The closed-image coordinates respect the S-algebra structure supplied by the actual
scheme projection to Spec S. -/
theorem actual_affine_rees_image_sections_coefficients (I : Ideal R) (s : S) :
    actualAffineReesImageSectionsEquiv (S := S) I
      (((actualAffineReesMap (S := S) I).ker.subschemeι ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (actualReesProjection I)).appTop ((Scheme.ΓSpecIso (.of S)).inv s)) =
      algebraMap S (reesAlgebra (I.map (algebraMap R S))) s := by
  have hc := ConcreteCategory.congr_hom
    (actual_affine_rees_section_coordinates_coefficients (S := S) I)
      ((Scheme.ΓSpecIso (.of S)).inv s)
  change (actualAffineReesSectionCoordinates (S := S) I).hom
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (actualReesProjection I)).appTop ((Scheme.ΓSpecIso (.of S)).inv s)) =
    algebraMap S (S ⊗[R] reesAlgebra I)
      ((Scheme.ΓSpecIso (.of S)).hom ((Scheme.ΓSpecIso (.of S)).inv s)) at hc
  have hs : (Scheme.ΓSpecIso (.of S)).hom ((Scheme.ΓSpecIso (.of S)).inv s) = s :=
    (Scheme.ΓSpecIso (.of S)).inv_hom_id_apply s
  rw [hs] at hc
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    actual_affine_rees_image_sections_equiv_inclusion]
  change actualReesBaseChangeMap I
    ((actualAffineReesSectionCoordinates (S := S) I).hom
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (actualReesProjection I)).appTop ((Scheme.ΓSpecIso (.of S)).inv s))) = _
  rw [hc]
  exact (actualReesBaseChangeMap (S := S) I).commutes s

end
end Negativity
