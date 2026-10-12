module
public import Linear.NormalizationSourceChartFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The actual Spec map on each complete homogeneous normalization chart
is finite, derived from finiteness of the original graded normalization. -/
theorem nativeNormalizationAffineChart_isFinite (a : R) (ha : a ∈ 𝒜 1) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))))) := by
  rw [IsFinite.SpecMap_iff]
  exact normalizationHomogeneousChart_finite 𝒜 𝓑 a ha

end LinearStudy
