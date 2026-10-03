module
public import Negativity.AffineOpenPullbackIdeal
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {R : Type u} [CommRing R]

/-- An actual ideal of R as an ideal sheaf on Spec R, using the canonical
coordinate-ring isomorphism rather than identifying the two rings by fiat. -/
def actualSpecIdealSheaf (I : Ideal R) : (Spec (.of R)).IdealSheafData :=
  IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)

@[simp]
theorem actual_spec_ideal_sheaf_top (I : Ideal R) :
    (actualSpecIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (.of R)).inv.hom := by
  simp [actualSpecIdealSheaf]

/-- Final theorem: the actual thickening by I^n has exactly the extended
power ideal in every actual affine source chart. The coefficient homomorphism
is the actual pullback of functions from Spec R. -/
theorem actual_spec_ideal_power_pullback_coordinates
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.affineOpens) (n : ℕ) :
    (((actualSpecIdealSheaf I) ^ n).comap f).ideal U =
      (I.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top).hom) ^ n := by
  rw [actual_affine_open_ideal_power_pullback, actual_spec_ideal_sheaf_top,
    Ideal.map_map, ← CommRingCat.hom_comp]

end
end Negativity
