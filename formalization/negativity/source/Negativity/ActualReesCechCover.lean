module
public import Negativity.ActualReesClosedOpenChart
public import Negativity.ActualProperCechCover
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

/-- The genuine affine cover of the relative Rees closed image induced by
an affine cover of the actual source scheme. -/
def actualReesCechCover (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) :
    ι → (actualRelativeReesScheme f I).affineOpens :=
  fun j => ⟨actualRelativeReesToSource f I ⁻¹ᵁ (U j).1,
    (U j).2.preimage (actualRelativeReesToSource f I)⟩

theorem actual_rees_cech_cover_covers (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) (hU : iSup (fun j => (U j).1) = ⊤) :
    iSup (fun j => (actualReesCechCover f I U j).1) = ⊤ := by
  exact (actualRelativeReesToSource f I).iSup_preimage_eq_top hU

theorem actual_rees_cech_chart_range (f : X ⟶ Spec (.of R)) (I : Ideal R)
    {ι : Type u} (U : ι → X.affineOpens) (j : ι) :
    (actualReesClosedOpenChart f I (U j).1).opensRange =
      (actualReesCechCover f I U j).1 :=
  actual_rees_closed_open_chart_range f I (U j).1

/-- Final theorem: properness supplies a finite source cover and, by
actual inverse images, a finite affine cover of the Rees closed image.
The pair and triple intersections are affine and the explicit local
Rees images embed as exactly those chart opens. -/
theorem exists_actual_rees_finite_affine_cech_cover
    (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R) :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.affineOpens),
      iSup (fun j => (U j).1) = ⊤ ∧
      (∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) ∧
      (∀ j k l, IsAffineOpen (((U j).1 ⊓ (U k).1) ⊓ (U l).1)) ∧
      iSup (fun j => (actualReesCechCover f I U j).1) = ⊤ ∧
      (∀ j k, IsAffineOpen
        ((actualReesCechCover f I U j).1 ⊓ (actualReesCechCover f I U k).1)) ∧
      (∀ j k l, IsAffineOpen
        (((actualReesCechCover f I U j).1 ⊓ (actualReesCechCover f I U k).1) ⊓
          (actualReesCechCover f I U l).1)) ∧
      (∀ j, (actualReesClosedOpenChart f I (U j).1).opensRange =
        (actualReesCechCover f I U j).1) := by
  obtain ⟨ι, hι, U, hcover, hpair, htriple⟩ := exists_actual_proper_affine_cech_cover f
  let : Fintype ι := hι
  refine ⟨ι, inferInstance, U, hcover, hpair, htriple,
    actual_rees_cech_cover_covers f I U hcover, ?_, ?_,
    actual_rees_cech_chart_range f I U⟩
  · intro j k
    exact (hpair j k).preimage (actualRelativeReesToSource f I)
  · intro j k l
    exact (htriple j k l).preimage (actualRelativeReesToSource f I)

end
end Negativity
