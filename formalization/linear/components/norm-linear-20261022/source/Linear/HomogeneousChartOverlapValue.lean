module
public import Linear.OriginalAwayOverlapFraction
public import Linear.NormalizationHomogeneousChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
universe u
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]

/-- The ACTUAL homogeneous Proj overlap restriction agrees, on original
values, with mathlib's actual full-localization overlap ring map. -/
theorem homogeneousChartOverlap_val
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (z : HomogeneousLocalization.Away 𝒜 a) :
    (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) z).val =
      (IsLocalization.Away.awayToAwayRight a b :
        Localization.Away a →+* Localization.Away (a*b)) z.val := by
  obtain ⟨n,x,hx,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha z
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk',Localization.mk_eq_mk',originalAwayOverlap_mk]
  congr 1
  exact mul_comm x (b^n)

end LinearStudy
