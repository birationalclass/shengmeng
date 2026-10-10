module
public import Linear.NativeProjectiveChartRefinement
public import Linear.NativeGradedModuleOverlapDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
variable (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ a : R, a ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → a • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule
include hgrade

/-- Every actual weighted degree-zero chart element gives an ACTUAL
associated-module sheaf section on its original basic open. -/
theorem nativeProjectiveChartDegreeZero_isSection
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeProjectiveModuleLocalPredicate 𝒜 𝒟 0).pred
      (nativeProjectiveChartRefinement 𝒜 a x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n,m,hm,rfl⟩ := hz
    intro p
    refine ⟨ProjectiveSpectrum.basicOpen 𝒜 a,p.property,
      𝟙 (ProjectiveSpectrum.basicOpen 𝒜 a),n*d,
      ⟨m,by simpa only [add_zero] using hm⟩,
      ⟨a^n,by simpa only [smul_eq_mul] using SetLike.pow_mem_graded n ha⟩,?_,?_⟩
    · intro q
      exact q.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem q.2 n
    · intro q
      exact originalLocalizedModuleRefinement_mk (Submonoid.powers a)
        q.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr q.2)
        m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)
  | zero =>
    have heq : nativeProjectiveChartRefinement 𝒜 a (0 : LocalizedModule (Submonoid.powers a) M) = 0 := by
      funext p
      exact (originalLocalizedModuleRefinement (Submonoid.powers a)
        p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2)).map_zero
    rw [heq]
    exact nativeProjectiveModuleLocalPredicate_zero 𝒜 𝒟 0 (ProjectiveSpectrum.basicOpen 𝒜 a)
  | add x y _ _ hx hy =>
    have heq : nativeProjectiveChartRefinement 𝒜 a (x+y) =
        nativeProjectiveChartRefinement 𝒜 a x + nativeProjectiveChartRefinement 𝒜 a y := by
      funext p
      exact (originalLocalizedModuleRefinement (Submonoid.powers a)
        p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2)).map_add x y
    rw [heq]
    exact nativeProjectiveModuleLocalPredicate_add 𝒜 𝒟 hgrade 0 hx hy
  | smul c x _ hx =>
    have hh := nativeProjectiveModuleLocalPredicate_smul 𝒜 𝒟 hgrade 0
      ((ProjectiveSpectrum.Proj.awayToSection 𝒜 a).hom c).property hx
    have heq : nativeProjectiveChartRefinement 𝒜 a (c • x) =
        (fun p => ((ProjectiveSpectrum.Proj.awayToSection 𝒜 a).hom c).val p •
          nativeProjectiveChartRefinement 𝒜 a x p) := by
      funext p
      exact nativeProjectiveChartRefinement_smul 𝒜 a c x p
    rw [heq]
    exact hh

/-- Bundle the constructed chart-to-sheaf comparison. Its scalar map is
mathlib's actual chart-to-structure-section map; no sheaf model is assumed. -/
def nativeProjectiveChartDegreeZeroSectionMap
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a
      →ₛₗ[(ProjectiveSpectrum.Proj.awayToSection 𝒜 a).hom]
        nativeProjectiveModuleSections 𝒜 𝒟 hgrade 0
          (op (ProjectiveSpectrum.basicOpen 𝒜 a)) where
  toFun x := ⟨nativeProjectiveChartRefinement 𝒜 a x.val,
    nativeProjectiveChartDegreeZero_isSection 𝒜 𝒟 hgrade d a ha x.val x.property⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact (originalLocalizedModuleRefinement (Submonoid.powers a)
      p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2)).map_add x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact nativeProjectiveChartRefinement_smul 𝒜 a c x.val p
end LinearStudy
