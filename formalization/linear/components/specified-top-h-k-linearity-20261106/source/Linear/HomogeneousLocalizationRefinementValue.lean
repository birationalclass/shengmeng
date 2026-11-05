module
public import Linear.NormalizationHomogeneousChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]

/-- The actual homogeneous restriction to a finer original denominator set
has the same value as the actual full-ring localization restriction. -/
theorem homogeneousLocalizationRefinement_val
    (P T : Submonoid R) (hPT : P ≤ T)
    (z : HomogeneousLocalization 𝒜 P) :
    (HomogeneousLocalization.mapId 𝒜 hPT z).val =
      IsLocalization.map (S := Localization P) (M := P) (T := T)
        (Localization T) (RingHom.id R) (fun _ hr => hPT hr) z.val := by
  obtain ⟨z,rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk,HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk',Localization.mk_eq_mk',IsLocalization.map_mk']
  rfl
end LinearStudy
