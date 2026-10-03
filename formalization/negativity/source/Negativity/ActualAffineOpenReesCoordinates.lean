module

public import Negativity.ActualReesClosedOpenChart
public import Negativity.ActualAffineReesImageCoordinates
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual categorical base-ring coefficient map on an open source chart. -/
abbrev actualAffineOpenCoefficientHom (f : X ⟶ Spec (.of R)) (U : X.Opens) :
    CommRingCat.of R ⟶ Γ(X,U) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top

/-- The actual base-ring coefficient map on an open source chart. -/
def actualAffineOpenCoefficientMap (f : X ⟶ Spec (.of R)) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (actualAffineOpenCoefficientHom f U).hom

@[instance_reducible]
def actualAffineOpenCoefficientAlgebra (f : X ⟶ Spec (.of R)) (U : X.Opens) :
    Algebra R Γ(X, U) :=
  (actualAffineOpenCoefficientMap f U).toAlgebra

/-- The actual affine chart lies over the Spec map of its actual coefficient homomorphism. -/
theorem actual_affine_open_coefficient_triangle (f : X ⟶ Spec (.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    hU.isoSpec.inv ≫ U.ι ≫ f =
      Spec.map (actualAffineOpenCoefficientHom f U) := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]

/-- Source-chart affine coordinates induce an actual base-change isomorphism. -/
def actualAffineOpenBaseChangeIso (f : X ⟶ Spec (.of R))
    (U : X.Opens) (hU : IsAffineOpen U) {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) :
    pullback (Spec.map (actualAffineOpenCoefficientHom f U)) g ≅
      pullback (U.ι ≫ f) g :=
  asIso (pullback.map _ _ _ _ hU.isoSpec.inv (𝟙 T) (𝟙 (Spec (.of R)))
    (by simpa only [Category.comp_id] using (actual_affine_open_coefficient_triangle f U hU).symm)
    (by simp))

/-- The actual polynomial-to-Rees maps agree under the actual chart-coordinate isomorphisms. -/
theorem actual_affine_open_rees_square (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    actualPolynomialReesMap (Spec.map (actualAffineOpenCoefficientHom f U)) I ≫
        (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom =
      (actualAffineOpenBaseChangeIso f U hU actualPolynomialProjection).hom ≫
        actualPolynomialReesMap (U.ι ≫ f) I := by
  apply pullback.hom_ext <;>
    simp [actualPolynomialReesMap, actualAffineOpenBaseChangeIso, pullback.map]

/-- The genuine image kernel transports through the affine coordinate isomorphism. -/
theorem actual_affine_open_rees_kernel (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualPolynomialReesMap (U.ι ≫ f) I).ker.comap
        (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom =
      (actualPolynomialReesMap
        (Spec.map (actualAffineOpenCoefficientHom f U)) I).ker := by
  have := actual_polynomial_rees_map_affine (U.ι ≫ f) I
  have hp : IsPullback
      (actualPolynomialReesMap
        (Spec.map (actualAffineOpenCoefficientHom f U)) I)
      (actualAffineOpenBaseChangeIso f U hU actualPolynomialProjection).hom
      (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom
      (actualPolynomialReesMap (U.ι ≫ f) I) :=
    IsPullback.of_vert_isIso ⟨actual_affine_open_rees_square f I U hU⟩
  apply IdealSheafData.ext
  funext V
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ hp V).symm

/-- The coordinate isomorphism acts on genuine scheme-theoretic images. -/
def actualAffineOpenImageCoordinatesMap (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    actualRelativeReesScheme
        (Spec.map (actualAffineOpenCoefficientHom f U)) I ⟶
      actualRelativeReesScheme (U.ι ≫ f) I :=
  IdealSheafData.subschemeMap _ _
    (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom
    (IdealSheafData.le_map_iff_comap_le.mpr
      (actual_affine_open_rees_kernel f I U hU).le)

@[reassoc (attr := simp)]
theorem actual_affine_open_image_coordinates_fac (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    actualAffineOpenImageCoordinatesMap f I U hU ≫
        (actualPolynomialReesMap (U.ι ≫ f) I).ker.subschemeι =
      (actualPolynomialReesMap
        (Spec.map (actualAffineOpenCoefficientHom f U)) I).ker.subschemeι ≫
        (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

instance actualAffineOpenImageCoordinatesMap_isIso (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (actualAffineOpenImageCoordinatesMap f I U hU) := by
  have hp : IsPullback
      (actualPolynomialReesMap
        (Spec.map (actualAffineOpenCoefficientHom f U)) I).ker.subschemeι
      (actualAffineOpenImageCoordinatesMap f I U hU)
      (actualAffineOpenBaseChangeIso f U hU (actualReesProjection I)).hom
      (actualPolynomialReesMap (U.ι ≫ f) I).ker.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · exact (actual_affine_open_image_coordinates_fac f I U hU).symm
    · simpa only [IdealSheafData.ker_subschemeι] using
        actual_affine_open_rees_kernel f I U hU
  exact hp.isIso_snd_of_isIso

/-- The actual open-image chart section comparison, using its proved image range. -/
def actualReesClosedOpenChartSections (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) :
    Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U) ≅
      Γ(actualRelativeReesScheme (U.ι ≫ f) I, ⊤) :=
  (actualRelativeReesScheme f I).presheaf.mapIso
      (eqToIso (by rw [Scheme.Hom.image_top_eq_opensRange, actual_rees_closed_open_chart_range])).op ≪≫
    (actualReesClosedOpenChart f I U).appIso ⊤


/-- The genuine closed-image chart covers the full preimage open. -/
theorem actual_rees_closed_open_chart_preimage (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) :
    actualReesClosedOpenChart f I U ⁻¹ᵁ
      (actualRelativeReesToSource f I ⁻¹ᵁ U) = ⊤ := by
  rw [← actual_rees_closed_open_chart_range, ← Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.preimage_image_eq]

theorem actual_rees_closed_open_chart_sections_hom (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) :
    (actualReesClosedOpenChartSections f I U).hom =
      (actualReesClosedOpenChart f I U).appLE
        (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
        (actual_rees_closed_open_chart_preimage f I U).ge := by
  simp only [actualReesClosedOpenChartSections, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE]

/-- The actual Rees closed-image sections over an arbitrary actual affine source open U are
exactly the Rees algebra of the ideal extended to Γ(X,U). -/
def actualAffineOpenReesSectionsEquiv (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U) ≃+*
      reesAlgebra (I.map (actualAffineOpenCoefficientMap f U)) := by
  let := actualAffineOpenCoefficientAlgebra f U
  let e := actualReesClosedOpenChartSections f I U ≪≫
    asIso (actualAffineOpenImageCoordinatesMap f I U hU).appTop
  exact e.commRingCatIsoToRingEquiv.trans
    (actualAffineReesImageSectionsEquiv (S := Γ(X,U)) I)

/-- The genuine chart-coordinate map respects the source projection. -/
theorem actual_affine_open_image_coordinates_source (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    actualAffineOpenImageCoordinatesMap f I U hU ≫ actualRelativeReesToSource (U.ι ≫ f) I =
      actualRelativeReesToSource
        (Spec.map (actualAffineOpenCoefficientHom f U)) I ≫ hU.isoSpec.inv := by
  dsimp only [actualRelativeReesToSource]
  rw [← Category.assoc, actual_affine_open_image_coordinates_fac]
  simp [actualAffineOpenBaseChangeIso, pullback.map]

/-- The actual closed open-chart map respects the source projection. -/
theorem actual_rees_closed_open_chart_source (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) :
    actualReesClosedOpenChart f I U ≫ actualRelativeReesToSource f I =
      actualRelativeReesToSource (U.ι ≫ f) I ≫ U.ι := by
  dsimp only [actualRelativeReesToSource]
  rw [← Category.assoc, actual_rees_closed_open_chart_fac]
  simp [actualBaseChangeOpenChart, pullback.map]

theorem actual_affine_open_rees_sections_equiv_apply (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U)
    (x : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U)) :
    letI := actualAffineOpenCoefficientAlgebra f U
    actualAffineOpenReesSectionsEquiv f I U hU x =
      actualAffineReesImageSectionsEquiv (S := Γ(X,U)) I
        ((actualAffineOpenImageCoordinatesMap f I U hU).appTop
          ((actualReesClosedOpenChart f I U).appLE
            (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
              (actual_rees_closed_open_chart_preimage f I U).ge x)) := by
  let := actualAffineOpenCoefficientAlgebra f U
  change actualAffineReesImageSectionsEquiv (S := Γ(X,U)) I
      ((actualAffineOpenImageCoordinatesMap f I U hU).appTop
        ((actualReesClosedOpenChartSections f I U).hom x)) = _
  rw [actual_rees_closed_open_chart_sections_hom]

/-- Transport of an actual section pullback across equality of scheme morphisms. -/
theorem actual_appLE_congr_morphism {Y Z : Scheme.{u}} {a b : Y ⟶ Z}
    (h : a = b) (U : Z.Opens) (V : Y.Opens) (e : V ≤ a ⁻¹ᵁ U) :
    a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst b
  rfl

/-- A source-function frame identity, proved for arbitrary actual schemes before specialization. -/
theorem actual_section_source_frame {Y W : Scheme.{u}} (p : W ⟶ X) (j : Y ⟶ W)
    (U : X.Opens) (hU : IsAffineOpen U) (q : Y ⟶ Spec Γ(X,U))
    (e : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ p ⁻¹ᵁ U) (hq : j ≫ p = q ≫ hU.fromSpec) :
    p.app U ≫ j.appLE (p ⁻¹ᵁ U) ⊤ e =
      (Scheme.ΓSpecIso Γ(X,U)).inv ≫ q.appTop := by
  rw [p.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    actual_appLE_congr_morphism hq, Scheme.Hom.comp_appLE q hU.fromSpec U ⊤,
    IsAffineOpen.fromSpec_app_self, Category.assoc]
  have hmap := Scheme.Hom.map_appLE' q (U := ⊤) (V := ⊤) le_rfl hU.fromSpec_preimage_self
  rw [hmap]
  simp [Scheme.Hom.appLE]

/-- The composite actual affine coordinate chart respects source functions. -/
theorem actual_affine_open_closed_chart_source (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualAffineOpenImageCoordinatesMap f I U hU ≫ actualReesClosedOpenChart f I U) ≫
        actualRelativeReesToSource f I =
      actualRelativeReesToSource (Spec.map (actualAffineOpenCoefficientHom f U)) I ≫
        hU.fromSpec := by
  rw [Category.assoc, actual_rees_closed_open_chart_source, ← Category.assoc,
    actual_affine_open_image_coordinates_source, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι]

/-- The composite chart has the full indicated open as preimage. -/
theorem actual_affine_open_closed_chart_preimage (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualAffineOpenImageCoordinatesMap f I U hU ≫ actualReesClosedOpenChart f I U) ⁻¹ᵁ
        actualRelativeReesToSource f I ⁻¹ᵁ U = ⊤ := by
  rw [Scheme.Hom.comp_preimage, actual_rees_closed_open_chart_preimage,
    TopologicalSpace.Opens.map_top]

/-- Global sections of a composite are the corresponding composite section pullbacks. -/
theorem actual_appLE_comp_top {Y Z W : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ W)
    (U : W.Opens) (e : (⊤ : Z.Opens) ≤ b ⁻¹ᵁ U)
    (e' : (⊤ : Y.Opens) ≤ (a ≫ b) ⁻¹ᵁ U) :
    b.appLE U ⊤ e ≫ a.appTop = (a ≫ b).appLE U ⊤ e' := by
  have hcoord : a.appTop = a.appLE ⊤ ⊤ le_rfl := by simp [Scheme.Hom.appLE]
  rw [hcoord, Scheme.Hom.appLE_comp_appLE]

/-- The actual chart section homomorphism is the section homomorphism of its composite. -/
theorem actual_affine_open_closed_chart_sections (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualReesClosedOpenChart f I U).appLE
        (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
          (actual_rees_closed_open_chart_preimage f I U).ge ≫
        (actualAffineOpenImageCoordinatesMap f I U hU).appTop =
      (actualAffineOpenImageCoordinatesMap f I U hU ≫ actualReesClosedOpenChart f I U).appLE
        (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
          (actual_affine_open_closed_chart_preimage f I U hU).ge := by
  exact actual_appLE_comp_top _ _ _ _ _


/-- The actual source-function frame on the concrete affine image chart. -/
theorem actual_affine_open_rees_source_frame (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) :
    (actualRelativeReesToSource f I).app U ≫
        (actualReesClosedOpenChart f I U).appLE
          (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
            (actual_rees_closed_open_chart_preimage f I U).ge ≫
        (actualAffineOpenImageCoordinatesMap f I U hU).appTop =
      (Scheme.ΓSpecIso Γ(X,U)).inv ≫
        (actualRelativeReesToSource
          (Spec.map (actualAffineOpenCoefficientHom f U)) I).appTop := by
  rw [actual_affine_open_closed_chart_sections]
  exact actual_section_source_frame _ _ U hU _ _
    (actual_affine_open_closed_chart_source f I U hU)

/-- Actual source functions become coefficient polynomials in the actual image coordinates. -/
theorem actual_affine_open_rees_sections_coefficients (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,U)) :
    actualAffineOpenReesSectionsEquiv f I U hU ((actualRelativeReesToSource f I).app U s) =
      algebraMap Γ(X,U) (reesAlgebra (I.map (actualAffineOpenCoefficientMap f U))) s := by
  let := actualAffineOpenCoefficientAlgebra f U
  rw [actual_affine_open_rees_sections_equiv_apply]
  have hs := ConcreteCategory.congr_hom (actual_affine_open_rees_source_frame f I U hU) s
  change (actualAffineOpenImageCoordinatesMap f I U hU).appTop
      ((actualReesClosedOpenChart f I U).appLE
        (actualRelativeReesToSource f I ⁻¹ᵁ U) ⊤
          (actual_rees_closed_open_chart_preimage f I U).ge
            ((actualRelativeReesToSource f I).app U s)) =
        (actualRelativeReesToSource
          (Spec.map (actualAffineOpenCoefficientHom f U)) I).appTop
            ((Scheme.ΓSpecIso Γ(X,U)).inv s) at hs
  rw [hs]
  exact actual_affine_rees_image_sections_coefficients I s

end
end Negativity
