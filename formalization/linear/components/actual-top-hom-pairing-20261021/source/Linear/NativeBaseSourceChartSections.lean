module
public import Linear.NativeGradedBaseSourceMap
public import Linear.NativeProjectiveChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The original degree-one chart module maps semilinearly to actual
sheaf sections with the actual chart-to-structure-sections scalar hom. -/
def nativeProjectiveZeroChartSectionMap (a : S) (ha : a ∈ 𝓑 1) :
    nativeGradedModuleAwayZero 𝓑 𝒟 a →ₛₗ[(Proj.awayToSection 𝓑 a).hom]
      nativeProjectiveModuleSections 𝓑 𝒟 hS 0 (op (Proj.basicOpen 𝓑 a)) where
  toFun x := nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS 1 a ha
    ⟨x.val,by simpa only [nativeGradedModuleAwayDegreeZero_one] using x.property⟩
  map_add' x y := (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS 1 a ha).map_add
    ⟨x.val,by simpa only [nativeGradedModuleAwayDegreeZero_one] using x.property⟩
    ⟨y.val,by simpa only [nativeGradedModuleAwayDegreeZero_one] using y.property⟩
  map_smul' c x := (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS 1 a ha).map_smulₛₗ c
    ⟨x.val,by simpa only [nativeGradedModuleAwayDegreeZero_one] using x.property⟩

/-- Construct the exact base-chart-to-original-source-section map,
retaining the original normalization scalar map. This is the local map
which must be glued, rather than an unspecified sections bijection. -/
def nativeBaseSourceChartSectionMap (a : R) (ha : a ∈ 𝒜 1) :
    nativeGradedModuleAwayZero 𝒜 𝒟 a
      →ₛₗ[((Proj.awayToSection 𝓑 (algebraMap R S a)).hom).comp
        (normalizationHomogeneousChartMap 𝒜 𝓑 a)]
      nativeProjectiveModuleSections 𝓑 𝒟 hS 0
        (op (Proj.basicOpen 𝓑 (algebraMap R S a))) := by
  let f := normalizationHomogeneousChartMap 𝒜 𝓑 a
  let g := (Proj.awayToSection 𝓑 (algebraMap R S a)).hom
  letI : RingHomCompTriple f g (g.comp f) := ⟨rfl⟩
  exact (nativeProjectiveZeroChartSectionMap 𝓑 𝒟 hS (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).comp
      (nativeGradedBaseSourceChartMap 𝒜 𝓑 𝒟 hR hS a ha)

theorem nativeBaseSourceChartSectionMap_value (a : R) (ha : a ∈ 𝒜 1)
    (x : nativeGradedModuleAwayZero 𝒜 𝒟 a)
    (p : Proj.basicOpen 𝓑 (algebraMap R S a)) :
    (nativeBaseSourceChartSectionMap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) a ha x).val p =
      nativeProjectiveChartRefinement 𝓑 (algebraMap R S a)
        (moduleBaseSourceLocalizationEquiv (S := S) a x.val) p := rfl

theorem nativeProjectiveZeroChartSectionMap_bijective (a : S) (ha : a ∈ 𝓑 1)
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS 1 a ha)) :
    Function.Bijective (nativeProjectiveZeroChartSectionMap 𝓑 𝒟 hS a ha) := by
  let e : nativeGradedModuleAwayZero 𝓑 𝒟 a ≃ nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 a :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by
      simp only [Equiv.refl_apply,nativeGradedModuleAwayDegreeZero_one])
  exact h.comp e.bijective

theorem nativeBaseSourceChartSectionMap_bijective (a : R) (ha : a ∈ 𝒜 1)
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS 1 (algebraMap R S a)
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    Function.Bijective (nativeBaseSourceChartSectionMap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) a ha) :=
  (nativeProjectiveZeroChartSectionMap_bijective 𝓑 𝒟 hS _ _ h).comp
    (nativeGradedBaseSourceChartMap_bijective 𝒜 𝓑 𝒟 hR hS a ha)
end LinearStudy
