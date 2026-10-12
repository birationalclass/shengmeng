module
public import Linear.NativeNormalizationProjectiveMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The ACTUAL original global normalization pulls chart functions back
by the SAME original complete homogeneous chart algebra map. -/
theorem nativeNormalizationProjectiveMap_chart_ring_square (a : R) (ha : a ∈ 𝒜 1) :
    Proj.awayToSection 𝒜 a ≫
      (nativeNormalizationProjectiveMap 𝒜 𝓑).appLE
        (Proj.basicOpen 𝒜 a) (Proj.basicOpen 𝓑 (algebraMap R S a)) le_rfl =
      CommRingCat.ofHom (algebraMap (HomogeneousLocalization.Away 𝒜 a)
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))) ≫
          Proj.awayToSection 𝓑 (algebraMap R S a) :=
  radicalProjMap_awayToSection_appLE (normalizationBaseGradedRingHom 𝒜 𝓑)
    (finiteGradedNormalization_irrelevant_le_radical 𝒜 𝓑) ha

/-- On the ACTUAL original global pushforward of any module sheaf,
the base chart scalar acts by the original pulled-back source-chart scalar. -/
theorem nativeNormalizationProjectiveMap_pushforward_chart_smul
    (a : R) (ha : a ∈ 𝒜 1) (M : (Proj 𝓑).Modules)
    (c : HomogeneousLocalization.Away 𝒜 a)
    (x : Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
      Proj.basicOpen 𝒜 a)) :
    (Proj.awayToSection 𝒜 a c) • x =
      (Proj.awayToSection 𝓑 (algebraMap R S a)
        (algebraMap (HomogeneousLocalization.Away 𝒜 a)
          (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) c)) •
        (show Γ(M,Proj.basicOpen 𝓑 (algebraMap R S a)) from x) := by
  have h := congr($(nativeNormalizationProjectiveMap_chart_ring_square 𝒜 𝓑 a ha) c)
  change (show Γ(Proj 𝓑,Proj.basicOpen 𝓑 (algebraMap R S a)) from
      (nativeNormalizationProjectiveMap 𝒜 𝓑).app (Proj.basicOpen 𝒜 a)
        (Proj.awayToSection 𝒜 a c)) •
      (show Γ(M,Proj.basicOpen 𝓑 (algebraMap R S a)) from x) = _
  congr 1

end LinearStudy
