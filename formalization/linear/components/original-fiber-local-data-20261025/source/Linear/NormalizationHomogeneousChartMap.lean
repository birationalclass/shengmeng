module
public import Linear.NativeDualDegreeZeroSpanValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]

/-- Bundle the ACTUAL normalization algebra map as a graded ring map,
using the original graded scalar action and the original unit. -/
@[reducible] def normalizationBaseGradedRingHom : 𝒜 →+*ᵍ 𝓑 where
  toRingHom := algebraMap R S
  map_mem := by
    intro n x hx
    simpa only [Algebra.smul_def, mul_one, vadd_eq_add, add_zero] using
      SetLike.GradedSMul.smul_mem hx (SetLike.one_mem_graded 𝓑)

/-- The actual map between homogeneous normalization/source chart rings. -/
def normalizationHomogeneousChartMap (a : R) :
    HomogeneousLocalization.Away 𝒜 a →+*
      HomogeneousLocalization.Away 𝓑 (algebraMap R S a) :=
  HomogeneousLocalization.Away.map (normalizationBaseGradedRingHom 𝒜 𝓑) a

/-- The actual homogeneous chart map has the original fraction formula. -/
theorem normalizationHomogeneousChartMap_mk
    (a : R) (ha : a ∈ 𝒜 1) (n : ℕ) (x : R) (hx : x ∈ 𝒜 n) :
    (normalizationHomogeneousChartMap 𝒜 𝓑 a
      (HomogeneousLocalization.Away.mk 𝒜 ha n x
        (by simpa only [smul_eq_mul, mul_one] using hx))).val =
      IsLocalization.mk' (M := Submonoid.powers (algebraMap R S a))
        (Localization.Away (algebraMap R S a)) (algebraMap R S x)
        ⟨(algebraMap R S a)^n,
          (Submonoid.powers (algebraMap R S a)).pow_mem (Submonoid.mem_powers _) n⟩ := by
  exact (congrArg HomogeneousLocalization.val
    (HomogeneousLocalization.Away.map_mk (normalizationBaseGradedRingHom 𝒜 𝓑)
      a ha n x (by simpa only [smul_eq_mul, mul_one] using hx))).trans
    (Localization.mk_eq_mk'_apply _ _)

end LinearStudy
