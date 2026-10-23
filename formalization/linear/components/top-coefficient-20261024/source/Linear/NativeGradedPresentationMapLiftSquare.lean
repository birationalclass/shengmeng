module
public import Linear.NativeProjectiveDegreeZeroComposition
public import Linear.IntegerShiftedFreePieces
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S I J M N : Type} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (w : I → ℤ) (v : J → ℤ)
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (hE : ∀ t : ℕ, ∀ d : ℤ, ∀ p : S, p ∈ B t →
  ∀ x : N, x ∈ E d → p • x ∈ E ((t:ℤ)+d))
variable (βM : (I → S) →ₗ[S] M) (βN : (J → S) →ₗ[S] N)
variable (hβM : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B w t → βM x ∈ D t)
variable (hβN : ∀ t : ℤ, ∀ x : J → S, x ∈ integerShiftedFreePiece B v t → βN x ∈ E t)
variable (e : M →ₗ[S] N) (he : ∀ t : ℤ, ∀ x : M, x ∈ D t → e x ∈ E t)
variable (τ : (I → S) →ₗ[S] (J → S))
variable (hτ : ∀ t : ℤ, ∀ x : I → S, x ∈ integerShiftedFreePiece B w t → τ x ∈ integerShiftedFreePiece B v t)
variable (hsquare : βN.comp τ=e.comp βM)
include hsquare

/-- An ORDINARY original graded module lift gives the ACTUAL original
native SHEAF map square on every original integer twist. Composition
of actual prime-localized maps is reused;no sheaf or Cech square assumed. -/
theorem nativeGradedPresentationMapLiftSquare (k : ℤ) :
    nativeProjectiveDegreeZeroSheafMap B (integerShiftedFreePiece B w) D
      (integerShiftedFreePiece_smul_homogeneous B w) hD βM hβM k ≫
      nativeProjectiveDegreeZeroSheafMap B D E hD hE e he k =
    nativeProjectiveDegreeZeroSheafMap B (integerShiftedFreePiece B w)
      (integerShiftedFreePiece B v) (integerShiftedFreePiece_smul_homogeneous B w)
      (integerShiftedFreePiece_smul_homogeneous B v) τ hτ k ≫
      nativeProjectiveDegreeZeroSheafMap B (integerShiftedFreePiece B v) E
        (integerShiftedFreePiece_smul_homogeneous B v) hE βN hβN k := by
  rw [nativeProjectiveDegreeZeroSheafMap_comp,nativeProjectiveDegreeZeroSheafMap_comp]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext p
  change nativeProjectiveModuleAtPrimeMap B (e.comp βM) p.1 (x.1 p) =
    nativeProjectiveModuleAtPrimeMap B (βN.comp τ) p.1 (x.1 p)
  rw [hsquare]

end LinearStudy
