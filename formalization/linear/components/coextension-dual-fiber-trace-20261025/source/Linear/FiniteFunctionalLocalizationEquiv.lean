module
public import Linear.FiniteFunctionalLocalization
public import Linear.FunctionalSourceLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
universe u
variable {R Q M : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (P : Submonoid R) [IsLocalization P Q]

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Actual localization of the finite dual, compared with the actual dual
of the localized source. No finite-free hypothesis is introduced. -/
def finiteFunctionalLocalizationEquiv (hinj : Function.Injective (algebraMap R Q)) :
    LocalizedModule P (M →ₗ[R] R) ≃ₗ[Q] (LocalizedModule P M →ₗ[Q] Q) := by
  let j := LinearMap.compRight (M := M) R (Algebra.linearMap R Q)
  letI : IsLocalizedModule P j :=
    finiteLinearFunctional_compRight_isLocalizedModule P hinj
  exact ((IsLocalizedModule.iso P j).extendScalarsOfIsLocalization P Q).trans
    (functionalSourceLocalizationEquiv P)

/-- The comparison is the canonical one: an integral functional evaluated
on an integral vector is the original value mapped to the localized ring. -/
theorem finiteFunctionalLocalizationEquiv_apply_mk
    (hinj : Function.Injective (algebraMap R Q)) (ψ : M →ₗ[R] R) (x : M) :
    finiteFunctionalLocalizationEquiv P hinj (LocalizedModule.mkLinearMap P _ ψ)
      (LocalizedModule.mkLinearMap P M x) = algebraMap R Q (ψ x) := by
  let j := LinearMap.compRight (M := M) R (Algebra.linearMap R Q)
  letI : IsLocalizedModule P j :=
    finiteLinearFunctional_compRight_isLocalizedModule P hinj
  change functionalSourceLocalizationEquiv P
    ((IsLocalizedModule.iso P j) (LocalizedModule.mk ψ 1))
      (LocalizedModule.mkLinearMap P M x) = _
  rw [functionalSourceLocalizationEquiv_apply_mk, IsLocalizedModule.iso_mk_one]
  rfl

end LinearStudy
