module
public import Mathlib.Algebra.Module.FinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace LinearStudy
universe u
variable {R M N N' : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup N'] [Module R N']

/-- Codomain localization of Hom for the original finitely presented
source is itself localization. No injectivity, freeness, domain or
nonzero denominator assumption is required, including the empty open. -/
theorem finitePresentationHom_codomain_isLocalizedModule
    [Module.FinitePresentation R M] (S : Submonoid R) (g : N →ₗ[R] N')
    [IsLocalizedModule S g] :
    IsLocalizedModule S (LinearMap.compRight (M := M) R g) := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    have hs := (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (S := S) (f := g) s)
    constructor
    · intro h k e
      exact LinearMap.ext fun m => hs.left congr($e m)
    · intro h
      use ((IsLocalizedModule.map_units (S := S) (f := g) s).unit⁻¹).1 ∘ₗ h
      ext x
      exact Module.End.isUnit_apply_inv_apply_of_isUnit
        (IsLocalizedModule.map_units (S := S) (f := g) s) (h x)
  · intro h
    obtain ⟨h',s,e⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S g h
    exact ⟨(h',s),e.symm⟩
  · intro h k e
    exact Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S g h k e
end LinearStudy
