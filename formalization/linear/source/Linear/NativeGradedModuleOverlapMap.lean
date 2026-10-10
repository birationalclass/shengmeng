module
public import Linear.NativeGradedModuleOverlapDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar

/-- Construct the actual degree-zero restriction map into the degree-two
overlap chart. Its scalar map is mathlib's actual homogeneous Proj map. -/
def nativeGradedModuleAwayZeroOverlapMap
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 d → b • m ∈ 𝒟 ((n : ℤ)+d))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) :
    nativeGradedModuleAwayZero 𝒜 𝒟 a
      →ₛₗ[HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)]
        nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b) where
  toFun x := ⟨originalLocalizedModuleAwayOverlap a b x.val,
    nativeGradedModuleAwayZero_overlap_mem 𝒜 𝒟 hgrade a b ha hb x.val x.property⟩
  map_add' x y := Subtype.ext ((originalLocalizedModuleAwayOverlap a b).map_add x.val y.val)
  map_smul' c x := Subtype.ext (originalHomogeneousModuleOverlap_smul 𝒜 a b ha hb c x.val)

/-- The constructed degree-zero overlap map retains the actual original
module restriction value. -/
theorem nativeGradedModuleAwayZeroOverlapMap_apply_val
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 d → b • m ∈ 𝒟 ((n : ℤ)+d))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (x : nativeGradedModuleAwayZero 𝒜 𝒟 a) :
    (nativeGradedModuleAwayZeroOverlapMap 𝒜 𝒟 hgrade a b ha hb x).val =
      originalLocalizedModuleAwayOverlap a b x.val := rfl
end LinearStudy
