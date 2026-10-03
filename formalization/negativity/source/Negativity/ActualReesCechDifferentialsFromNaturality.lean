module
public import Negativity.ActualReesCechCoordinates
public import Negativity.ActualGradedClosedCechQuotient
public import Negativity.ActualCechAmbientModule

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def actualReesSectionCoefficient (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U) →+ Γ(X,U) :=
  (Polynomial.lcoeff Γ(X,U) n).toAddMonoidHom.comp
    ((reesAlgebra (I.map (actualAffineOpenCoefficientMap f U))).val.toAddMonoidHom.comp
      (actualAffineOpenReesSectionsEquiv f I U hU).toAddMonoidHom)

theorem actualReesSectionCoefficient_apply (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U)) :
    actualReesSectionCoefficient f I U hU n a =
      (actualAffineOpenReesSectionsEquiv f I U hU a).1.coeff n := rfl

theorem actualCechDifference_apply {T : Scheme.{u}} {ι : Type u}
    (V : ι → T.Opens) (b : actualCechZero T V) (j k : ι) :
    actualCechDifference T V b j k = actualSectionRestriction T inf_le_right (b k) -
      actualSectionRestriction T inf_le_left (b j) := rfl

theorem actualCechBoundary_apply {T : Scheme.{u}} {ι : Type u}
    (V : ι → T.Opens) (a : actualCechOne T V) (j k l : ι) :
    actualCechBoundary T V a j k l =
      actualSectionRestriction T (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a k l) -
      actualSectionRestriction T (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a j l) +
      actualSectionRestriction T inf_le_left (a j k) := rfl

theorem actualCechTwo_zero_apply {T : Scheme.{u}} {ι : Type u}
    (V : ι → T.Opens) (j k l : ι) : (0 : actualCechTwo T V) j k l = 0 := rfl

/-- A local coordinate compatibility statement. The geometric instance is
proved separately from the actual chart projection triangles. -/
def ActualReesCoordinateRestrictionCompatibility (f : X ⟶ Spec (.of R)) (I : Ideal R) : Prop :=
  ∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (a : Γ(actualRelativeReesScheme f I, actualRelativeReesToSource f I ⁻¹ᵁ U)) (n : ℕ),
    actualReesSectionCoefficient f I V hV n
      (actualSectionRestriction (actualRelativeReesScheme f I)
        ((actualRelativeReesToSource f I).preimage_mono h) a) =
      actualSectionRestriction X h
        (actualReesSectionCoefficient f I U hU n a)

theorem actual_rees_cech_difference_coeff_from_naturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (b : actualCechZero (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (n : ℕ) :
    (actualReesCechOneEquiv f I U hpair
      (actualCechDifference (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) b) n).1 =
      actualCechDifference X (fun j => (U j).1)
        (actualReesCechZeroEquiv f I U b n).1 := by
  funext j k
  rw [actualReesCechOneEquiv_coeff, ← actualReesSectionCoefficient_apply,
    actualCechDifference_apply]
  rw [(actualReesSectionCoefficient f I _ (hpair j k) n).map_sub]
  have hk := hnat (U k).1 ((U j).1 ⊓ (U k).1) (U k).2 (hpair j k) inf_le_right (b k) n
  have hj := hnat (U j).1 ((U j).1 ⊓ (U k).1) (U j).2 (hpair j k) inf_le_left (b j) n
  erw [hk, hj]
  rw [actualCechDifference_apply, actualReesCechZeroEquiv_coeff,
    actualReesCechZeroEquiv_coeff, actualReesSectionCoefficient_apply,
    actualReesSectionCoefficient_apply]

theorem actual_rees_cech_boundary_coeff_from_naturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (a : actualCechOne (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) (n : ℕ) (j k l : ι) :
    (actualAffineOpenReesSectionsEquiv f I (((U j).1 ⊓ (U k).1) ⊓ (U l).1)
      (htriple j k l) (actualCechBoundary (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) a j k l)).1.coeff n =
      actualCechBoundary X (fun j => (U j).1)
        (actualReesCechOneEquiv f I U hpair a n).1 j k l := by
  rw [← actualReesSectionCoefficient_apply, actualCechBoundary_apply]
  rw [(actualReesSectionCoefficient f I _ (htriple j k l) n).map_add,
    (actualReesSectionCoefficient f I _ (htriple j k l) n).map_sub]
  have hkl := hnat ((U k).1 ⊓ (U l).1) _ (hpair k l) (htriple j k l)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a k l) n
  have hjl := hnat ((U j).1 ⊓ (U l).1) _ (hpair j l) (htriple j k l)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a j l) n
  have hjk := hnat ((U j).1 ⊓ (U k).1) _ (hpair j k) (htriple j k l) inf_le_left (a j k) n
  erw [hkl, hjl, hjk]
  rw [actualCechBoundary_apply, actualReesCechOneEquiv_coeff,
    actualReesCechOneEquiv_coeff, actualReesCechOneEquiv_coeff,
    actualReesSectionCoefficient_apply, actualReesSectionCoefficient_apply,
    actualReesSectionCoefficient_apply]

theorem actual_rees_cech_cycle_iff_from_naturality
    (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (hnat : ActualReesCoordinateRestrictionCompatibility f I)
    {ι : Type u} [Fintype ι] (U : ι → X.affineOpens)
    (hpair : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (htriple : ∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1))
    (a : actualCechOne (actualRelativeReesScheme f I)
      (fun j => (actualReesCechCover f I U j).1)) :
    actualCechBoundary (actualRelativeReesScheme f I)
        (fun j => (actualReesCechCover f I U j).1) a = 0 ↔
      ∀ n, actualCechBoundary X (fun j => (U j).1)
        (actualReesCechOneEquiv f I U hpair a n).1 = 0 := by
  constructor
  · intro ha n
    funext j k l
    rw [← actual_rees_cech_boundary_coeff_from_naturality f I hnat U hpair htriple,
      ha]
    rw [actualCechTwo_zero_apply, actualCechTwo_zero_apply,
      ← actualReesSectionCoefficient_apply, map_zero]
  · intro ha
    funext j k l
    apply (actualAffineOpenReesSectionsEquiv f I _ (htriple j k l)).injective
    apply Subtype.ext
    ext n
    rw [actual_rees_cech_boundary_coeff_from_naturality f I hnat U hpair htriple,
      ha n]
    rw [actualCechTwo_zero_apply, actualCechTwo_zero_apply,
      ← actualReesSectionCoefficient_apply, map_zero]

#print axioms actual_rees_cech_difference_coeff_from_naturality
#print axioms actual_rees_cech_boundary_coeff_from_naturality
#print axioms actual_rees_cech_cycle_iff_from_naturality
end
end Negativity

