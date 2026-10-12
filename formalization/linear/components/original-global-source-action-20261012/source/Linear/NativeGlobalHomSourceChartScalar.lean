module
public import Linear.NativeGlobalHomSourceChartModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
theorem nativeNormalizationGlobalHomSourceChartModule_smul
    (a : R) (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf),Proj.basicOpen 𝒜 a)) :
    letI := nativeNormalizationGlobalHomSourceChartModule 𝒜 𝓑 a
    b • h = schemePushforwardHomSourceActionSection (nativeNormalizationProjectiveMap 𝒜 𝓑)
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) (Proj.basicOpen 𝒜 a)
      ((Proj.awayToSection 𝓑 (algebraMap R S a)) b) h := rfl
end LinearStudy
