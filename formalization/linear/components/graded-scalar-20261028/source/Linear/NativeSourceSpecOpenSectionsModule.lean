module
public import Linear.NativeProjectiveModuleSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ,∀ d : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D d → c • x ∈ D ((n : ℤ)+d))
/-- Actual affine-chart scalar action on sections over ANY actual Spec open.
This names the existing native modulesSpecToSheaf action once,so later proofs
do not repeatedly unfold its complete instance at each restriction. -/
@[instance_reducible] def nativeSourceSpecOpenSectionsModule
    (a : S) (ha : a ∈ B 1)
    (W : (Spec (CommRingCat.of (HomogeneousLocalization.Away B a))).Opens) :
    Module (HomogeneousLocalization.Away B a)
      Γ((nativeProjectiveModuleSheaf B D hD 0).restrict (Proj.awayι B a ha (by decide)),W) :=
  inferInstanceAs <| Module (HomogeneousLocalization.Away B a)
    (((modulesSpecToSheaf (R := CommRingCat.of (HomogeneousLocalization.Away B a))).obj
      ((nativeProjectiveModuleSheaf B D hD 0).restrict (Proj.awayι B a ha (by decide)))).obj.obj (op W))
end LinearStudy
