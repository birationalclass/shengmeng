module
public import Linear.NativeProjectiveModuleSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (DG : ℤ → Submodule K D) (EG : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ ell : D, ell ∈ DG d → b • ell ∈ DG ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ B n →
  ∀ ell : E, ell ∈ EG d → b • ell ∈ EG ((n : ℤ)+d))

/-- The original homogeneous injection gives an ACTUAL sheaf monomorphism
from degree zero into degree delta. The target identification uses the
proved integer equality 0+delta=delta, not an implicit large type conversion. -/
theorem nativeProjectiveHomogeneousInjection_exists_zero_degree_mono
    (delta : ℤ) (e : D →ₗ[S] E)
    (hh : ∀ d : ℤ, ∀ ell : D, ell ∈ DG d → e ell ∈ EG (d+delta))
    (he : Function.Injective e) :
    ∃ j : nativeProjectiveModuleSheaf B DG hD 0 ⟶
      nativeProjectiveModuleSheaf B EG hE delta, Mono j := by
  let f := nativeProjectiveModuleSheafMap B DG EG hD hE delta e hh 0
  letI : Mono f := nativeProjectiveModuleSheafMap_mono B DG EG hD hE delta e hh he 0
  let targetIso : nativeProjectiveModuleSheaf B EG hE (0+delta) ≅
      nativeProjectiveModuleSheaf B EG hE delta :=
    eqToIso (congrArg (nativeProjectiveModuleSheaf B EG hE) (zero_add delta))
  exact ⟨f ≫ targetIso.hom,inferInstance⟩
end LinearStudy
