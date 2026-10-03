module

public import Negativity.ProjectiveAffineChartAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

def actualProjectiveAffineChartInclusion (R : Type u) [CommRing R] (n : ℕ) :
    Spec (.of (actualProjectiveAffineChart R n)) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  Proj.awayι _ (MvPolynomial.X (0 : Fin (n + 1)))
    (MvPolynomial.isHomogeneous_X R _) Nat.zero_lt_one

instance (R : Type u) [CommRing R] (n : ℕ) :
    IsOpenImmersion (actualProjectiveAffineChartInclusion R n) := by
  unfold actualProjectiveAffineChartInclusion
  infer_instance

theorem actual_projective_affine_chart_inclusion_over
    (R : Type u) [CommRing R] (n : ℕ) :
    actualProjectiveAffineChartInclusion R n ≫ actualProjectiveSpaceToSpec R n =
      Spec.map (CommRingCat.ofHom (actualProjectiveChartConstant R n)) := by
  simp only [actualProjectiveAffineChartInclusion, actualProjectiveSpaceToSpec,
    ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Final theorem: an actual finite-type morphism between actual affine
schemes admits an actual locally closed immersion into standard relative
projective space. Its genuine structure morphism is the given map over
the base's canonical affine identification. Polynomial generators and
the actual standard-chart quotient construct the immersion. -/
theorem exists_actual_affine_finite_type_projective_immersion
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (j : X ⟶ Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(Y, ⊤))),
      IsImmersion j ∧ j ≫ actualProjectiveSpaceToSpec Γ(Y, ⊤) n = f ≫ Y.toSpecΓ := by
  let R := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  letI : Algebra R B := f.appTop.hom.toAlgebra
  have hf : f.appTop.hom.FiniteType := by
    simpa! [Scheme.Hom.appLE, Scheme.Hom.appTop] using
      f.finiteType_appLE (isAffineOpen_top Y) (isAffineOpen_top X) (by simp)
  have : Algebra.FiniteType R B := hf
  obtain ⟨n, φ, hφ, hbase⟩ := exists_actual_projective_affine_chart_quotient R B
  let j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ actualProjectiveAffineChartInclusion R n
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  refine ⟨n, j, by dsimp [j]; infer_instance, ?_⟩
  dsimp [j]
  rw [Category.assoc, Category.assoc, actual_projective_affine_chart_inclusion_over,
    ← Spec.map_comp]
  have hb : CommRingCat.ofHom (actualProjectiveChartConstant R n) ≫
      CommRingCat.ofHom φ = f.appTop := by
    apply CommRingCat.hom_ext
    exact hbase
  rw [hb]
  exact (Scheme.toSpecΓ_naturality f).symm

end
end Negativity
