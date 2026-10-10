module
public import Linear.NormalizationHomogeneousChartProduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Normalize an ORIGINAL homogeneous component into its actual source
Proj chart. Addition is proved inside the original ring localization. -/
def normalizationChartHomogeneousAddMap (a : S) (ha : a ∈ 𝓑 1) (n : ℕ) :
    𝓑 n →+ HomogeneousLocalization.Away 𝓑 a where
  toFun b := HomogeneousLocalization.Away.mk 𝓑 ha n b (by simpa using b.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  map_add' := by
    intro b c
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.val_add,
      HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.Away.val_mk]
    exact (Localization.add_mk_self _ _ _).symm

theorem normalizationChartHomogeneousAddMap_apply
    (a : S) (ha : a ∈ 𝓑 1) (n : ℕ) (b : 𝓑 n) :
    normalizationChartHomogeneousAddMap 𝓑 a ha n b =
      HomogeneousLocalization.Away.mk 𝓑 ha n b (by simpa using b.property) := rfl
end LinearStudy
