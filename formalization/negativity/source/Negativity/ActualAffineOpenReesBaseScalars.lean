module
public import Negativity.ActualAffineReesBaseScalarCoordinates
public import Negativity.ActualAffineOpenReesCoordinates
public import Negativity.ActualCechSections

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

theorem actual_affine_open_image_coordinates_base (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    actualAffineOpenImageCoordinatesMap f I U hU ≫ actualRelativeReesToBase (U.ι ≫ f) I =
      actualRelativeReesToBase (Spec.map (actualAffineOpenCoefficientHom f U)) I := by
  dsimp only [actualRelativeReesToBase]
  rw [← Category.assoc, actual_affine_open_image_coordinates_fac]
  simp [actualAffineOpenBaseChangeIso, pullback.map]

theorem actual_rees_closed_open_chart_base (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) :
    actualReesClosedOpenChart f I U ≫ actualRelativeReesToBase f I =
      actualRelativeReesToBase (U.ι ≫ f) I := by
  dsimp only [actualRelativeReesToBase]
  rw [← Category.assoc, actual_rees_closed_open_chart_fac]
  simp [actualBaseChangeOpenChart, pullback.map]

theorem actual_affine_open_closed_chart_base (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualAffineOpenImageCoordinatesMap f I U hU ≫ actualReesClosedOpenChart f I U) ≫
        actualRelativeReesToBase f I =
      actualRelativeReesToBase (Spec.map (actualAffineOpenCoefficientHom f U)) I := by
  rw [Category.assoc, actual_rees_closed_open_chart_base,
    actual_affine_open_image_coordinates_base]

theorem actual_appTop_restriction {Y Z : Scheme.{u}} (g : Y ⟶ Z) (V : Y.Opens) :
    g.appTop ≫ Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
      g.appLE ⊤ V le_top := by
  have hg : g.appTop = g.appLE ⊤ ⊤ le_rfl := by simp [Scheme.Hom.appLE]
  rw [hg, Scheme.Hom.appLE_map]

theorem actual_section_base_frame {Y W B : Scheme.{u}} (p : W ⟶ B) (j : Y ⟶ W)
    (V : W.Opens) (q : Y ⟶ B) (e : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ V)
    (hq : j ≫ p = q) :
    p.appLE ⊤ V le_top ≫ j.appLE V ⊤ e = q.appTop := by
  rw [Scheme.Hom.appLE_comp_appLE, actual_appLE_congr_morphism hq]
  simp [Scheme.Hom.appLE]

theorem actual_affine_open_rees_base_frame (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualRelativeReesToBase f I).appLE ⊤ (actualRelativeReesToSource f I ⁻¹ᵁ U) le_top ≫
        (actualReesClosedOpenChart f I U).appLE
          (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
            (actual_rees_closed_open_chart_preimage f I U).ge ≫
        (actualAffineOpenImageCoordinatesMap f I U hU).appTop =
      (actualRelativeReesToBase (Spec.map (actualAffineOpenCoefficientHom f U)) I).appTop := by
  rw [actual_affine_open_closed_chart_sections]
  exact actual_section_base_frame _ _ _ _ _
    (actual_affine_open_closed_chart_base f I U hU)

/-- The actual Rees chart coordinates respect every genuine base Rees scalar.
This identifies the full scalar ring used in proper cohomology, not only degree zero. -/
theorem actual_affine_open_rees_sections_base_scalars (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) (p : reesAlgebra I) :
    letI := actualAffineOpenCoefficientAlgebra f U
    actualAffineOpenReesSectionsEquiv f I U hU
      (actualSectionRestriction (actualRelativeReesScheme f I) le_top
        ((actualRelativeReesToBase f I).appTop
          ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p))) =
      actualReesCoefficientMap (S := Γ(X,U)) I p := by
  let := actualAffineOpenCoefficientAlgebra f U
  rw [actual_affine_open_rees_sections_equiv_apply]
  have hs := ConcreteCategory.congr_hom (actual_affine_open_rees_base_frame f I U hU)
    ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)
  have hr := ConcreteCategory.congr_hom
    (actual_appTop_restriction (actualRelativeReesToBase f I)
      (actualRelativeReesToSource f I ⁻¹ᵁ U))
    ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv p)
  change actualSectionRestriction (actualRelativeReesScheme f I) le_top
    ((actualRelativeReesToBase f I).appTop _) =
      (actualRelativeReesToBase f I).appLE ⊤ _ le_top _ at hr
  rw [hr]
  change actualAffineReesImageSectionsEquiv (S := Γ(X,U)) I
    ((actualAffineOpenImageCoordinatesMap f I U hU).appTop
      ((actualReesClosedOpenChart f I U).appLE _ ⊤ _
        ((actualRelativeReesToBase f I).appLE ⊤ _ le_top _))) = _
  change (actualAffineOpenImageCoordinatesMap f I U hU).appTop
    ((actualReesClosedOpenChart f I U).appLE _ ⊤ _
      ((actualRelativeReesToBase f I).appLE ⊤ _ le_top _)) = _ at hs
  rw [hs]
  exact actual_affine_rees_image_sections_base_scalars I p

#print axioms actual_affine_open_rees_sections_base_scalars
end
end Negativity
