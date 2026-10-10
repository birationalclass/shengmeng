module
public import Linear.NormalizationChartHomogeneousAddMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- An arbitrary ACTUAL source-chart functional is homogenized on each
original graded component. Its values lie in the original base localization. -/
def normalizationChartFunctionalHomogeneousAddMap
    (a : R) (haB : algebraMap R S a ∈ 𝓑 1)
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a)
    (n : ℕ) : 𝓑 n →+ Localization.Away a where
  toFun b := (algebraMap R (Localization.Away a) a)^n *
    (f (normalizationChartHomogeneousAddMap 𝓑 (algebraMap R S a) haB n b)).val
  map_zero' := by
    rw [map_zero,map_zero,HomogeneousLocalization.val_zero,mul_zero]
  map_add' := by
    intro b c
    rw [map_add,map_add,HomogeneousLocalization.val_add,mul_add]

/-- Extend the original homogeneous-piece construction by the ACTUAL
graded decomposition of S. No source functional or free basis is supplied. -/
def normalizationChartFunctionalAddMap
    (a : R) (haB : algebraMap R S a ∈ 𝓑 1)
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) :
    S →+ Localization.Away a :=
  (DirectSum.toAddMonoid
    (normalizationChartFunctionalHomogeneousAddMap 𝒜 𝓑 a haB f)).comp
    (DirectSum.decomposeAddEquiv 𝓑).toAddMonoidHom

/-- The extension retains its prescribed value on every ORIGINAL
homogeneous element, not only a selected collection of generators. -/
theorem normalizationChartFunctionalAddMap_homogeneous
    (a : R) (haB : algebraMap R S a ∈ 𝓑 1)
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a)
    (n : ℕ) (b : S) (hb : b ∈ 𝓑 n) :
    normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f b =
      (algebraMap R (Localization.Away a) a)^n *
        (f (HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb))).val := by
  change DirectSum.toAddMonoid
    (normalizationChartFunctionalHomogeneousAddMap 𝒜 𝓑 a haB f)
    (DirectSum.decompose 𝓑 b) = _
  rw [DirectSum.decompose_of_mem 𝓑 hb,DirectSum.toAddMonoid_of]
  rfl
end LinearStudy
