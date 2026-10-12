module
public import Linear.NativeProjectiveModuleTwistTensorMap
public import Linear.ModuleSheafificationLocalCriterion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- Actual homogeneous multiplication on the genuine tensor SHEAF,
constructed by the module-sheafification adjunction from the proved
fraction pairing. No sheaf comparison is supplied as an input. -/
def nativeProjectiveModuleTwistTensorSheafMap (m : ℕ) (k : ℤ) :
    nativeProjectiveModuleTwistTensorSheaf 𝓑 𝒟 hD m k ⟶
      nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(m : ℤ)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj)).symm
      (nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k)

/-- The global tensor-sheaf map induces exactly the original bilinear
fraction multiplication before sheafification. -/
theorem nativeProjectiveModuleTwistTensorSheafMap_pairing (m : ℕ) (k : ℤ) :
    PresheafOfModules.sheafificationHomEquiv
      (𝟙 (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj)
      (nativeProjectiveModuleTwistTensorSheafMap 𝓑 𝒟 hD m k) =
    nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k :=
  Equiv.apply_symm_apply _ _

end LinearStudy
