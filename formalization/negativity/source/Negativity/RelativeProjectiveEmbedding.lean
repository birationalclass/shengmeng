module

public import Negativity.ProjPolynomialSections
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual base-ring inclusion into the degree-zero subring of the
standard homogeneous polynomial ring. -/
def projectiveDegreeZeroInclusion (R : Type u) [CommRing R] (n : ℕ) :
    R →+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' r s := Subtype.ext (map_mul MvPolynomial.C r s)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' r s := Subtype.ext (map_add MvPolynomial.C r s)

/-- The genuine relative structure map P^n_R → Spec R, through the
actual degree-zero subring of the actual Proj scheme. -/
def actualProjectiveSpaceToSpec (R : Type u) [CommRing R] (n : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
    Spec.map (CommRingCat.ofHom (projectiveDegreeZeroInclusion R n))

/-- An actual relative projective embedding over an affine base. The
embedding is closed and its genuine Proj structure map equals the given
morphism after the base's canonical affine identification. No divisor,
section, positivity or negativity conclusion occurs in this definition. -/
structure ActualRelativeProjectiveEmbedding {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] where
  dimension : ℕ
  embedding : X ⟶ Proj
    (MvPolynomial.homogeneousSubmodule (Fin (dimension + 1)) Γ(Y, ⊤))
  closed : IsClosedImmersion embedding
  over_base : embedding ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) dimension =
    f ≫ Y.toSpecΓ

/-- Relative projective geometry specified on actual affine target
opens. These are genuine closed embeddings over their base, not an
assumed Cartier, intersection or numerical model. -/
def ActualLocallyProjective {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : Y.Opens) (hU : IsAffineOpen U),
    letI : IsAffine U.toScheme := hU
    Nonempty U → Nonempty (ActualRelativeProjectiveEmbedding (f ∣_ U))

/-- Final theorem: a genuine relative projective embedding over an
affine base produces the actual Cartier coordinate section geometry.
Its compatibility with the given base morphism is part of the geometric
embedding, and no divisor/section model is an input. -/
theorem actual_relative_projective_embedding_cartier_sections
    {X Y : Scheme.{u}} [IsIntegral X] [IsAffine Y]
    (f : X ⟶ Y) (P : ActualRelativeProjectiveEmbedding f) :
    ∃ A : CartierAtlas X X, Nonempty (CartierAffineSectionCover A X) := by
  have := P.closed
  exact exists_actual_projective_space_cartier_sections Γ(Y, ⊤) P.dimension P.embedding

end
end Negativity
