module
public import Linear.RadicalProjMap
public import Linear.NormalizationHomogeneousChartMap
public import Linear.FiniteGradedNormalizationIrrelevantRadical
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
/-- Finiteness derives the source cover by images of base coordinates,
using the actual radical Proj morphism. Base coordinates only generate R. -/
theorem nativeFiniteNormalization_sourceCoordinateCover [Module.Finite R S]
    {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤) :
    (⨆ i,Proj.basicOpen B (algebraMap R S (a i))) = ⊤ := by
  let p := radicalProjMap (normalizationBaseGradedRingHom A B)
    (finiteGradedNormalization_irrelevant_le_radical A B)
  have h := p.iSup_preimage_eq_top (degreeOneGenerated_nativeProj_cover A a ha hgenR)
  exact h
end LinearStudy
