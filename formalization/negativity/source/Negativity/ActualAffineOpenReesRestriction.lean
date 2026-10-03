module
public import Negativity.ActualAffineOpenReesCoordinates
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

/-- The genuine ring restriction on scheme sections. -/
def actualOpenSectionsRestriction {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) :
    Γ(Y,U) →+* Γ(Y,V) :=
  (Y.presheaf.map (homOfLE h).op).hom

/-- The genuine section restriction on source-preimage Rees charts. -/
def actualReesOpenSectionsRestriction (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {U V : X.Opens} (h : V ≤ U) :
    Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U) →+*
      Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ V) :=
  (((actualRelativeReesScheme f I).presheaf.map
    ((Opens.map (actualRelativeReesToSource f I).base).map (homOfLE h)).op)).hom

/-- Base coefficients commute with genuine source-section restriction. -/
theorem actual_affine_open_coefficient_restriction (f : X ⟶ Spec (.of R))
    {U V : X.Opens} (h : V ≤ U) :
    actualAffineOpenCoefficientMap f V =
      (actualOpenSectionsRestriction h).comp (actualAffineOpenCoefficientMap f U) := by
  have hc : actualAffineOpenCoefficientHom f U ≫ X.presheaf.map (homOfLE h).op =
      actualAffineOpenCoefficientHom f V := by
    dsimp only [actualAffineOpenCoefficientHom]
    rw [Category.assoc, Scheme.Hom.appLE_map]
  ext r
  exact (ConcreteCategory.congr_hom hc r).symm

/-- Actual morphism pullback and actual section restriction commute. -/
theorem actual_open_sections_restriction_source {Y : Scheme.{u}} (p : Y ⟶ X)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(X,U)) :
    (((Y.presheaf.map ((Opens.map p.base).map (homOfLE h)).op)).hom) (p.app U s) =
      p.app V (actualOpenSectionsRestriction h s) := by
  exact (ConcreteCategory.congr_hom (p.naturality (homOfLE h).op) s).symm

/-- Recovering a section after a proved coordinate equality is independent of representation. -/
theorem actual_ring_equiv_symm_of_apply {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) (b : B) (h : e a = b) : e.symm b = a := by
  rw [← h, RingEquiv.symm_apply_apply]

/-- The inverse actual coordinates recover genuine source functions. -/
theorem actual_affine_open_rees_sections_symm_coefficients (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,U)) :
    (actualAffineOpenReesSectionsEquiv f I U hU).symm
      (algebraMap Γ(X,U) (reesAlgebra (I.map (actualAffineOpenCoefficientMap f U))) s) =
      (actualRelativeReesToSource f I).app U s :=
  actual_ring_equiv_symm_of_apply _ _ _
    (actual_affine_open_rees_sections_coefficients f I U hU s)

/-- Actual source coefficient generators restrict to the expected coefficient polynomials. -/
theorem actual_affine_open_rees_restriction_coefficients (f : X ⟶ Spec (.of R))
    (I : Ideal R) {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (s : Γ(X,U)) :
    (actualAffineOpenReesSectionsEquiv f I V hV
      (actualReesOpenSectionsRestriction f I h
        ((actualAffineOpenReesSectionsEquiv f I U hU).symm
          (algebraMap Γ(X,U) (reesAlgebra (I.map (actualAffineOpenCoefficientMap f U))) s)))).1 =
      C (actualOpenSectionsRestriction h s) := by
  rw [actual_affine_open_rees_sections_symm_coefficients]
  have hn := actual_open_sections_restriction_source (actualRelativeReesToSource f I) h s
  change actualReesOpenSectionsRestriction f I h ((actualRelativeReesToSource f I).app U s) =
    (actualRelativeReesToSource f I).app V (actualOpenSectionsRestriction h s) at hn
  rw [hn, actual_affine_open_rees_sections_coefficients]
  rfl

/-- Global scalar pullbacks commute with section restriction on any actual scheme. -/
theorem actual_appLE_top_restriction {Y Z : Scheme.{u}} (q : Y ⟶ Z)
    (A B : Y.Opens) (i : Opposite.op A ⟶ Opposite.op B) (z : Γ(Z,⊤)) :
    Y.presheaf.map i (q.appLE ⊤ A le_top z) = q.appLE ⊤ B le_top z := by
  exact ConcreteCategory.congr_hom (q.appLE_map le_top i) z

/-- Genuine base Rees scalar pullbacks restrict to the same genuine global scalar. -/
theorem actual_rees_sections_restrict_base (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {U V : X.Opens} (h : V ≤ U) (z : Γ(Spec (.of (reesAlgebra I)),⊤)) :
    actualReesOpenSectionsRestriction f I h
      ((actualRelativeReesToBase f I).appLE ⊤ (actualRelativeReesToSource f I ⁻¹ᵁ U) le_top z) =
      (actualRelativeReesToBase f I).appLE ⊤ (actualRelativeReesToSource f I ⁻¹ᵁ V) le_top z :=
  actual_appLE_top_restriction _ _ _ _ z

/-- The coefficientwise base Rees map is natural for actual source-section restrictions. -/
theorem actual_rees_coefficient_map_restriction (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {U V : X.Opens} (h : V ≤ U) (p : reesAlgebra I) :
    let := actualAffineOpenCoefficientAlgebra f U
    let := actualAffineOpenCoefficientAlgebra f V
    (actualReesCoefficientMap (S := Γ(X,V)) I p).1 =
      (actualReesCoefficientMap (S := Γ(X,U)) I p).1.map (actualOpenSectionsRestriction h) := by
  let := actualAffineOpenCoefficientAlgebra f U
  let := actualAffineOpenCoefficientAlgebra f V
  change p.1.map (actualAffineOpenCoefficientMap f V) =
    (p.1.map (actualAffineOpenCoefficientMap f U)).map (actualOpenSectionsRestriction h)
  rw [Polynomial.map_map, actual_affine_open_coefficient_restriction f h]

end
end Negativity
