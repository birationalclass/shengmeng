module
public import Linear.KoszulFunctionResolution
public import Mathlib.Algebra.Group.Action.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Appending a unit makes every connecting map of the actual Koszul
homology sequence bijective: it is a unit times the actual shift isomorphism. -/
theorem koszul_append_unit_delta_bijective (φ : M →ₗ[R] R) (a : R) (ha : IsUnit a) (i : ℕ) :
    Function.Bijective ((koszulComplex.shortComplexProd_shortExact φ a).δ (i+1) i rfl) := by
  rw [koszulComplex.shortComplexProd_δ_eq]
  change Function.Bijective (fun x => ((-1 : R)^i*a) • (koszulComplex.upOneHomologyIso φ i).hom x)
  exact ((isUnit_neg_one.pow i).mul ha).smul_bijective.comp
    (koszulComplex.upOneHomologyIso φ i).toLinearEquiv.bijective

/-- The same actual exterior-power Koszul complex is exact in every
positive degree when one appended equation is a unit. No regularity
or proper-ideal hypothesis is imposed on the other equations. -/
theorem koszul_append_unit_exactAt (φ : M →ₗ[R] R) (a : R) (ha : IsUnit a)
    (i : ℕ) (hi : 0 < i) : (koszulComplex (koszulComplex.appendMap φ a)).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let hS := koszulComplex.shortComplexProd_shortExact φ a
  have hδepi (j : ℕ) : Epi (hS.δ (j+1) j rfl) :=
    (ModuleCat.epi_iff_surjective _).mpr (koszul_append_unit_delta_bijective φ a ha j).surjective
  have hδmono (j : ℕ) : Mono (hS.δ (j+1) j rfl) :=
    (ModuleCat.mono_iff_injective _).mpr (koszul_append_unit_delta_bijective φ a ha j).injective
  have hf := (hS.homology_exact₁ (i+1) i rfl).epi_f_iff.mp (hδepi i)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hg := (hS.homology_exact₃ (j+1) j rfl).mono_g_iff.mp (hδmono j)
  exact (hS.homology_exact₂ (j+1)).isZero_X₂ hf hg

end LinearStudy
