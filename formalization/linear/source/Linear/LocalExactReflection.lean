module
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Exact.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open TensorProduct
variable {R : Type*} [CommRing R]
variable {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- Genuine local-to-global exactness for actual module maps, using the
existing submodule membership local criterion and actual tensor localization.
No finite generation or smoothness hypothesis is needed. -/
theorem linearMaps_exact_of_baseChange_exact_maximal
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hzero : g.comp f=0)
    (hlocal : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Exact (f.baseChange (Localization.AtPrime P))
        (g.baseChange (Localization.AtPrime P))) : Function.Exact f g := by
  intro x
  constructor
  · intro hx
    change x ∈ LinearMap.range f
    apply Submodule.mem_of_localization_maximal
      (fun (P : Ideal R) (_ : P.IsMaximal) => Localization.AtPrime P ⊗[R] M₁)
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) M₁ 1)
    intro P hP
    let A := Localization.AtPrime P
    let l₀ := TensorProduct.mk R A M₀ 1
    let l₁ := TensorProduct.mk R A M₁ 1
    have hf : IsLocalizedModule.map P.primeCompl l₀ l₁ f=
        (f.baseChange A).restrictScalars R := by
      apply IsLocalizedModule.linearMap_ext P.primeCompl l₀ l₁
      ext z
      simpa [l₀,l₁,LinearMap.baseChange_tmul] using
        IsLocalizedModule.map_apply P.primeCompl l₀ l₁ f z
    rw [← LinearMap.range_localizedMap_eq_localized₀_range P.primeCompl l₀ l₁ f,hf]
    change (1 : A) ⊗ₜ[R] x ∈ LinearMap.range ((f.baseChange A).restrictScalars R)
    exact (hlocal P ((1 : A) ⊗ₜ[R] x)).mp (by simp [hx])
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun hzero y

end LinearStudy
