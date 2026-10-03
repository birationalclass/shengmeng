module

public import Negativity.ReesBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R : Type u} [CommRing R]

abbrev actualReesProjection (I : Ideal R) : Spec (.of (reesAlgebra I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (reesAlgebra I)))

abbrev actualPolynomialProjection : Spec (.of R[X]) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R[X]))

def actualPolynomialToRees (I : Ideal R) :
    Spec (.of R[X]) ⟶ Spec (.of (reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (reesAlgebra I).val.toRingHom)

theorem actual_polynomial_rees_triangle (I : Ideal R) :
    actualPolynomialToRees I ≫ actualReesProjection I = actualPolynomialProjection := by
  dsimp [actualPolynomialToRees, actualReesProjection, actualPolynomialProjection]
  rw [← Spec.map_comp]
  rfl

def actualPolynomialReesMap {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    pullback f actualPolynomialProjection ⟶ pullback f (actualReesProjection I) :=
  pullback.map _ _ _ _ (𝟙 X) (actualPolynomialToRees I) (𝟙 (Spec (.of R)))
    (by simp) (by simp [actual_polynomial_rees_triangle])

abbrev actualRelativeReesScheme {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    Scheme.{u} := (actualPolynomialReesMap f I).ker.subscheme

def actualRelativeReesToBase {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    actualRelativeReesScheme f I ⟶ Spec (.of (reesAlgebra I)) :=
  (actualPolynomialReesMap f I).ker.subschemeι ≫ pullback.snd f (actualReesProjection I)

theorem actual_polynomial_rees_map_affine {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (I : Ideal R) : IsAffineHom (actualPolynomialReesMap f I) := by
  have : IsAffineHom (actualPolynomialProjection (R := R)) := by
    dsimp [actualPolynomialProjection]
    infer_instance
  have : IsAffineHom (actualReesProjection I) := by
    dsimp [actualReesProjection]
    infer_instance
  have hm : actualPolynomialReesMap f I ≫ pullback.fst f (actualReesProjection I) =
      pullback.fst f actualPolynomialProjection := by
    simp [actualPolynomialReesMap]
  have : IsAffineHom (actualPolynomialReesMap f I ≫ pullback.fst f (actualReesProjection I)) := by
    rw [hm]
    exact MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom (pullback.fst f (actualReesProjection I)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact IsAffineHom.of_comp _ (pullback.fst f (actualReesProjection I))

/-- Final theorem: the scheme-theoretic image of the actual polynomial
map inside the Rees base change is proper over the actual Rees ring.
It is constructed as a genuine closed subscheme of the proper base
change, rather than postulated as a relative spectrum. Identifying its
affine coordinate rings and Čech cohomology is separate work. -/
theorem actual_relative_rees_scheme_proper {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R) :
    IsProper (actualRelativeReesToBase f I) := by
  dsimp [actualRelativeReesToBase]
  infer_instance

end
end Negativity
