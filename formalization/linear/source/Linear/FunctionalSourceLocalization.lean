module
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
universe u
variable {R Q M : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
variable [AddCommGroup M] [Module R M]
variable (P : Submonoid R) [IsLocalization P Q]

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Restrict an actual localized-source functional along the actual
module localization map. Scalars are still in the localized ring. -/
def functionalSourceLocalizationRestriction :
    (LocalizedModule P M →ₗ[Q] Q) →ₗ[Q] (M →ₗ[R] Q) where
  toFun φ := (φ.restrictScalars R).comp (LocalizedModule.mkLinearMap P M)
  map_add' := by intro φ ψ; ext x; rfl
  map_smul' := by intro q φ; ext x; rfl

/-- The localization universal property gives exactly the localized-source
functional. This requires neither finiteness nor freeness of the source. -/
theorem functionalSourceLocalizationRestriction_bijective :
    Function.Bijective (functionalSourceLocalizationRestriction (Q := Q) (M := M) P) := by
  have hQ : ∀ s : P, IsUnit (algebraMap R (Module.End R Q) s) :=
    IsLocalizedModule.map_units (Algebra.linearMap R Q)
  constructor
  · intro φ ψ h
    have hR : φ.restrictScalars R = ψ.restrictScalars R :=
      IsLocalizedModule.ext P (LocalizedModule.mkLinearMap P M) hQ h
    ext x
    exact LinearMap.congr_fun hR x
  · intro φ
    let l := LocalizedModule.lift P φ hQ
    refine ⟨l.extendScalarsOfIsLocalization P Q, ?_⟩
    ext x
    exact LocalizedModule.lift_mk_one P φ hQ x

/-- Actual extension from the original source to its localization,
with the full localized-ring linear structure. -/
def functionalSourceLocalizationEquiv :
    (M →ₗ[R] Q) ≃ₗ[Q] (LocalizedModule P M →ₗ[Q] Q) :=
  (LinearEquiv.ofBijective
    (functionalSourceLocalizationRestriction (Q := Q) (M := M) P)
    (functionalSourceLocalizationRestriction_bijective (Q := Q) (M := M) P)).symm

theorem functionalSourceLocalizationEquiv_apply_mk (φ : M →ₗ[R] Q) (x : M) :
    functionalSourceLocalizationEquiv P φ (LocalizedModule.mkLinearMap P M x) = φ x := by
  exact LinearMap.congr_fun
    ((LinearEquiv.ofBijective
      (functionalSourceLocalizationRestriction (Q := Q) (M := M) P)
      (functionalSourceLocalizationRestriction_bijective (Q := Q) (M := M) P)).apply_symm_apply φ) x

end LinearStudy
