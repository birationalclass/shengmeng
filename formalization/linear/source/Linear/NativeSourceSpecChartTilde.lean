module
public import Linear.NativeSourceSpecChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
  nativeSourceSpecChartSectionsModule

/-- Actual source module sheaf on its Spec chart, built through the SAME fraction sections. -/
def nativeSourceSpecChartTildeIso (a : S) (ha : a ∈ 𝓑 1)
    [(nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).IsQuasicoherent]
    (h : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha)) :
    tilde (ModuleCat.of (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))
      (nativeGradedModuleAwayZero 𝓑 𝒟 a)) ≅
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict
        (Proj.awayι 𝓑 a ha (by decide)) := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let P : (Spec R).Modules := (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict
    (Proj.awayι 𝓑 a ha (by decide))
  let E := LinearEquiv.ofBijective (nativeSourceSpecChartSectionLinearMap 𝓑 𝒟 hD a ha)
    (nativeSourceSpecChartSectionLinearMap_bijective 𝓑 𝒟 hD a ha h)
  let e : ModuleCat.of R (nativeGradedModuleAwayZero 𝓑 𝒟 a) ≅
      (moduleSpecΓFunctor (R := R)).obj P := E.toModuleIso
  letI : P.IsQuasicoherent := inferInstance
  exact (tilde.functor R).mapIso e ≪≫ asIso P.fromTildeΓ

end LinearStudy
