module
public import Linear.NativeProjectiveModuleTwistPairing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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

/-- The actual sectionwise tensor presheaf of the two native module sheaves. -/
def nativeProjectiveModuleTwistTensorPresheaf (m : ℕ) (k : ℤ) :
    PresheafOfModules.{u} (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := (AlgebraicGeometry.Proj 𝓑).sheaf.obj)
    (nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ))
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hD k)

/-- Actual bilinear fraction multiplication induces a morphism from the
actual sectionwise tensor presheaf, with all restrictions proved. -/
def nativeProjectiveModuleTwistTensorPresheafMap (m : ℕ) (k : ℤ) :
    nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k ⟶
      nativeProjectiveModulePresheaf 𝓑 𝒟 hD (k+(m : ℤ)) where
  app U := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U
    letI := nativeProjectiveModuleSectionModule 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD (k+(m : ℤ)) U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD (k+(m : ℤ)) U
    exact ModuleCat.ofHom
      (X := (nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k).obj U)
      (Y := (nativeProjectiveModulePresheaf 𝓑 𝒟 hD (k+(m : ℤ))).obj U)
      (TensorProduct.lift
      (nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U))
  naturality i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro r ell
    exact (nativeProjectiveModuleTwistPairing_restrict 𝓑 𝒟 hD m k i r ell).symm

/-- The genuine tensor sheaf is the sheafification of the actual tensor
presheaf, via mathlib's module-sheafification functor. -/
def nativeProjectiveModuleTwistTensorSheaf (m : ℕ) (k : ℤ) :
    (AlgebraicGeometry.Proj 𝓑).Modules :=
  (PresheafOfModules.sheafification (𝟙 (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj)).obj
    (nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k)

end LinearStudy
