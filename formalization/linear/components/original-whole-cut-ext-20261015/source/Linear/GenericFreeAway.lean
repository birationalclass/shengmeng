module
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy

/-- A finite module over a Noetherian domain is free on a constructed
nonempty principal open, with its actual generic rank. -/
theorem finiteModule_exists_free_away
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization.Away r) (LocalizedModule.Away r M) =
        Module.finrank R M := by
  let K := FractionRing R
  let N := K ⊗[R] M
  let l : M →ₗ[R] N := TensorProduct.mk R K M 1
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨r, hr, hfree, hdim⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) l K
  have hd : Module.finrank K N = Module.finrank R M :=
    (IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl).trans
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R) l le_rfl)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree, hdim.trans hd⟩

end LinearStudy
