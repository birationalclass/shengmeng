module
public import Linear.NativeProjectiveOriginalBaseScalarMap
public import Linear.NativeProjectiveCechCoefficientObjects
public import Linear.NativeProjectiveModuleSheaf
public import Linear.NativeProjectiveModuleScalarApply
public import Linear.ProjBasicOpenBaseScalar
public import Linear.SchemeModuleActualAbelianScalarValue
public import Mathlib.Topology.Sheaves.Forget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] originalGlobalModuleScalar
open CategoryTheory.Limits
variable {ι : Type u} [LinearOrder ι] (U : ι → (Proj 𝓑).Opens)
attribute [local irreducible] orderedFormalCechComplex FormalCoproduct.evalOp
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
/-- Name the ORIGINAL ordered Cech map of the ORIGINAL base-global scalar.
The coefficient action and the actual ordered Cech complex are unchanged. -/
def nativeProjectiveOrderedBaseScalarMap (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  orderedTopAbelianCechCoefficientMap (Proj 𝓑) U
    (nativeProjectiveOriginalBaseScalarMap 𝓑 𝒟 hgrade k r)
end LinearStudy
