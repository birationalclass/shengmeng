module
public import Linear.NativeProjectiveOrderedBaseScalarMap
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.SchemeModuleActualHObjects
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
/-- The EXACT original scalar coefficient map on ordered Cech homology. -/
def nativeProjectiveOrderedCechHomologyBaseScalarMap (k : ℤ) (n : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  HomologicalComplex.homologyMap (nativeProjectiveOrderedBaseScalarMap 𝓑 𝒟 hgrade U k r) n
/-- The EXACT actual H map induced by the ORIGINAL O-linear global scalar.
This only names the existing coefficient functor; no action is transported. -/
def nativeProjectiveActualHBaseScalarMap (k : ℤ) (n : ℕ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  schemeModuleActualHCoefficientHom
    (originalGlobalModuleScalar
      ((Proj.toSpecZero 𝓑 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝓑 0)))).appTop r)
      (nativeProjectiveModuleSheaf 𝓑 𝒟 hgrade k)) n
end LinearStudy
