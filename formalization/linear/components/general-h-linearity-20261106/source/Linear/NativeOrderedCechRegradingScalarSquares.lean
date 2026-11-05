module
public import Linear.NativeProjectiveOrderedBaseScalarMap
public import Linear.OrderedCechIsoOriginalScalar
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
attribute [local irreducible] nativeProjectiveTwistRegradingIso orderedTopAbelianCechCoefficientMap orderedTopAbelianCechCoefficientIso
/-- Regrading hom square on the original actual ordered complexes. -/
def nativeProjectiveOrderedCechRegrading_baseScalar_hom_square (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  show CommSq _ _ _ _ from
    ⟨orderedTopAbelianCechCoefficientIso_moduleScalar_hom U
      ((Proj.toSpecZero 𝓑 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝓑 0)))).appTop r)
      (nativeProjectiveTwistRegradingIso 𝓑 𝒟 hgrade k)⟩
/-- Inverse regrading square with the same original coefficient action. -/
def nativeProjectiveOrderedCechRegrading_baseScalar_inv_square (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  show CommSq _ _ _ _ from
    ⟨orderedTopAbelianCechCoefficientIso_moduleScalar_inv U
      ((Proj.toSpecZero 𝓑 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝓑 0)))).appTop r)
      (nativeProjectiveTwistRegradingIso 𝓑 𝒟 hgrade k)⟩
end LinearStudy
