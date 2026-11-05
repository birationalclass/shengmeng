module
public import Linear.NativeGradedModuleOverlapDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar

/-- The actual homogeneous overlap formula allows arbitrary homogeneous
degrees. In particular it applies to intersections of several charts. -/
theorem homogeneousChartWeightedOverlap_val
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
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

/-- Semilinearity of the actual module restriction on arbitrary-degree
charts, with the actual homogeneous ring restriction as scalar map. -/
theorem originalHomogeneousModuleWeightedOverlap_smul
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (c : HomogeneousLocalization.Away 𝒜 a)
    (x : LocalizedModule (Submonoid.powers a) M) :
    originalLocalizedModuleAwayOverlap a b (c • x) =
      HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) c •
        originalLocalizedModuleAwayOverlap a b x := by
  change originalLocalizedModuleAwayOverlap a b (c.val • x) =
    (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) c).val •
      originalLocalizedModuleAwayOverlap a b x
  rw [originalLocalizedModuleAwayOverlap_smul,
    homogeneousChartWeightedOverlap_val 𝒜 d e a b ha hb]

/-- The original degree-zero numerator has degree n*d on the a chart
and degree n*(d+e) after restriction to the a*b chart. -/
theorem nativeGradedModuleWeightedOverlap_mem
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    originalLocalizedModuleAwayOverlap a b x ∈
      nativeGradedModuleAwayDegreeZero 𝒜 𝒟 (d+e) (a*b) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n,m,hm,rfl⟩ := hz
    rw [originalLocalizedModuleAwayOverlap_mk]
    apply Submodule.subset_span
    refine ⟨n,b^n • m,?_,rfl⟩
    have hp : b^n ∈ 𝒜 (n*e) := by
      simpa only [smul_eq_mul] using SetLike.pow_mem_graded n hb
    have hd := hgrade (n*e) ((n*d : ℕ) : ℤ) (b^n) hp m hm
    simpa only [mul_add,Int.natCast_add,add_comm] using hd
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [originalHomogeneousModuleWeightedOverlap_smul 𝒜 d e a b ha hb]
    exact Submodule.smul_mem _ _ hx

/-- Actual weighted degree-zero overlap map. No abstract restriction or
degree-preservation certificate is supplied as an input. -/
def nativeGradedModuleWeightedOverlapMap
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a
      →ₛₗ[HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)]
        nativeGradedModuleAwayDegreeZero 𝒜 𝒟 (d+e) (a*b) where
  toFun x := ⟨originalLocalizedModuleAwayOverlap a b x.val,
    nativeGradedModuleWeightedOverlap_mem 𝒜 𝒟 hgrade d e a b ha hb x.val x.property⟩
  map_add' x y := Subtype.ext ((originalLocalizedModuleAwayOverlap a b).map_add x.val y.val)
  map_smul' c x := Subtype.ext
    (originalHomogeneousModuleWeightedOverlap_smul 𝒜 d e a b ha hb c x.val)
end LinearStudy
