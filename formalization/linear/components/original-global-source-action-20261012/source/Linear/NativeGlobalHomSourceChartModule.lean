module
public import Linear.NativeNormalizationProjectiveMap
public import Linear.PushforwardHomSourceActionModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Source chart scalars act through original Proj chart functions and
the proved source-module structure on the SAME original Hom sections. -/
@[instance_reducible] def nativeNormalizationGlobalHomSourceChartModule (a : R) :
    Module (HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
      Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
          (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
        (SheafOfModules.unit (Proj 𝒜).ringCatSheaf),Proj.basicOpen 𝒜 a) := by
  let f := nativeNormalizationProjectiveMap 𝒜 𝓑
  let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := Γ(schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
    N,Proj.basicOpen 𝒜 a)
  letI : SMul (Γ(Proj 𝓑,f ⁻¹ᵁ Proj.basicOpen 𝒜 a)) H :=
    ⟨schemePushforwardHomSourceActionSection f N (Proj.basicOpen 𝒜 a)⟩
  letI : Module (Γ(Proj 𝓑,f ⁻¹ᵁ Proj.basicOpen 𝒜 a)) H :=
    schemePushforwardHomSourceModule f N (Proj.basicOpen 𝒜 a)
  letI : Module (Γ(Proj 𝓑,Proj.basicOpen 𝓑 (algebraMap R S a))) H := by
    change Module (Γ(Proj 𝓑,f ⁻¹ᵁ Proj.basicOpen 𝒜 a)) H
    exact schemePushforwardHomSourceModule f N (Proj.basicOpen 𝒜 a)
  exact Module.compHom H (Proj.awayToSection 𝓑 (algebraMap R S a)).hom

end LinearStudy
