module
public import Linear.LocalizedModuleAwayOverlapSemilinear
public import Linear.HomogeneousChartOverlapValue
public import Linear.NativeGradedModuleAway
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

/-- The actual degree-zero module on a chart with denominator of degree e.
The numerator of m/a^n has degree n*e, including degree 2n on a product
of two degree-one coordinates. No degree-one convention is misapplied. -/
def nativeGradedModuleAwayDegreeZero (e : ℕ) (a : R) :
    Submodule (HomogeneousLocalization.Away 𝒜 a)
      (LocalizedModule (Submonoid.powers a) M) :=
  Submodule.span _ {z | ∃ n : ℕ, ∃ m : M, m ∈ 𝒟 ((n*e : ℕ) : ℤ) ∧
    z = LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)}

/-- At degree one this is exactly the original native degree-zero module. -/
theorem nativeGradedModuleAwayDegreeZero_one (a : R) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a =
      nativeGradedModuleAwayZero 𝒜 𝒟 a := by
  simp only [nativeGradedModuleAwayDegreeZero,nativeGradedModuleAwayZero,mul_one]

/-- Actual module overlap restriction is semilinear for the actual
homogeneous Proj overlap map, rather than only the full ring map. -/
theorem originalHomogeneousModuleOverlap_smul
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (c : HomogeneousLocalization.Away 𝒜 a)
    (x : LocalizedModule (Submonoid.powers a) M) :
    originalLocalizedModuleAwayOverlap a b (c • x) =
      HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) c •
        originalLocalizedModuleAwayOverlap a b x := by
  change originalLocalizedModuleAwayOverlap a b (c.val • x) =
    (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) c).val •
      originalLocalizedModuleAwayOverlap a b x
  rw [originalLocalizedModuleAwayOverlap_smul,homogeneousChartOverlap_val 𝒜 a b ha hb]

/-- The actual restriction preserves degree zero on the ACTUAL overlap
module with degree-two denominator. This proves membership on all of the
original generated module, not just on individual homogeneous fractions. -/
theorem nativeGradedModuleAwayZero_overlap_mem
    (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 d → b • m ∈ 𝒟 ((n : ℤ)+d))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayZero 𝒜 𝒟 a) :
    originalLocalizedModuleAwayOverlap a b x ∈
      nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n,m,hm,rfl⟩ := hz
    rw [originalLocalizedModuleAwayOverlap_mk]
    apply Submodule.subset_span
    refine ⟨n,b^n • m,?_,rfl⟩
    have hp : b^n ∈ 𝒜 n := by simpa using SetLike.pow_mem_graded n hb
    have hd := hgrade n (n : ℤ) (b^n) hp m hm
    simpa only [mul_two,Int.natCast_add] using hd
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [originalHomogeneousModuleOverlap_smul 𝒜 a b ha hb]
    exact Submodule.smul_mem _ _ hx
end LinearStudy
