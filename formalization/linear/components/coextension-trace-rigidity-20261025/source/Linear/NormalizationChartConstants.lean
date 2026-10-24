module
public import Linear.NormalizationHomogeneousChartMap
public import Linear.AwayCongr
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
/-- The actual normalization chart map preserves the original degree-zero
constants, by the native homogeneous-localization map formula. -/
theorem normalizationHomogeneousChartMap_fromZero (a : R) (r : A 0) :
    normalizationHomogeneousChartMap A B a
      (HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a) r) =
    HomogeneousLocalization.fromZeroRingHom B (Submonoid.powers (algebraMap R S a))
      ⟨algebraMap R S r,(normalizationBaseGradedRingHom A B).map_mem r.property⟩ :=
  awayMap_fromZeroRingHom (normalizationBaseGradedRingHom A B) a r
/-- In particular the actual chart map preserves the original ground-field
constants. This uses the ORIGINAL scalar tower, not a desired H-linearity. -/
theorem normalizationHomogeneousChartMap_baseConstant (a : R) (r : K) :
    normalizationHomogeneousChartMap A B a
      (HomogeneousLocalization.fromZeroRingHom A (Submonoid.powers a) (algebraMap K (A 0) r)) =
    HomogeneousLocalization.fromZeroRingHom B (Submonoid.powers (algebraMap R S a))
      (algebraMap K (B 0) r) := by
  rw [normalizationHomogeneousChartMap_fromZero]
  congr 1
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply K R S r).symm
end LinearStudy
