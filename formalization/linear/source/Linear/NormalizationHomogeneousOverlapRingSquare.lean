module
public import Linear.NormalizationHomogeneousChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
/-- The ACTUAL base/source affine normalization maps commute with the
ACTUAL homogeneous overlap maps in all degrees. No ring-square hypothesis is supplied. -/
theorem normalizationHomogeneousChartMap_overlap_square
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) :
    (normalizationHomogeneousChartMap 𝒜 𝓑 (a*b)).comp
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)) =
    (HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)).comp
        (normalizationHomogeneousChartMap 𝒜 𝓑 a) := by
  apply RingHom.ext
  intro z
  obtain ⟨n,x,hx,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha z
  simp only [RingHom.comp_apply]
  rw [HomogeneousLocalization.awayMap_mk]
  have hleft := HomogeneousLocalization.Away.map_mk
    (normalizationBaseGradedRingHom 𝒜 𝓑) (a*b) (SetLike.mul_mem_graded ha hb)
    n (x*b^n) (by rw [smul_add]; exact SetLike.mul_mem_graded hx (SetLike.pow_mem_graded n hb))
  have hright := HomogeneousLocalization.Away.map_mk
    (normalizationBaseGradedRingHom 𝒜 𝓑) a ha n x hx
  refine Eq.trans hleft (Eq.trans ?_
    (congrArg (HomogeneousLocalization.awayMap 𝓑
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb)
      (map_mul (algebraMap R S) a b)) hright).symm)
  rw [HomogeneousLocalization.awayMap_mk]
  congr 1
  exact map_mul (algebraMap R S) x (b^n) |>.trans
    (congrArg ((algebraMap R S) x * ·) (map_pow (algebraMap R S) b n))
/-- The actual base ratio used to localize an overlap maps to the SAME
source ratio, allowing native affine finite-dual localization on the actual overlap. -/
theorem normalizationHomogeneousChartMap_overlap_localization_element
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) :
    normalizationHomogeneousChartMap 𝒜 𝓑 a
      (HomogeneousLocalization.Away.isLocalizationElem ha hb) =
    HomogeneousLocalization.Away.isLocalizationElem
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb) := by
  exact (HomogeneousLocalization.Away.map_mk
    (normalizationBaseGradedRingHom 𝒜 𝓑) a ha e (b^d)
    (by convert SetLike.pow_mem_graded d hb using 2; exact mul_comm _ _)).trans (by
      congr 1
      exact map_pow (algebraMap R S) b d)
end LinearStudy
