module
public import Linear.FiniteCoextensionModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual coextension dual is finite also as an upper-ring module;
the base-ring finiteness is proved, then restriction of scalars is enlarged. -/
theorem coextensionDual_finite_upper [IsNoetherianRing R] [Module.Finite R S] :
    Module.Finite S
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : Module R D := Module.compHom D (algebraMap R S)
  letI : IsScalarTower R S D := ⟨by
    intro a b ell
    change (a • b : S) • ell = algebraMap R S a • (b • ell)
    rw [Algebra.smul_def,mul_smul]⟩
  letI : Module.Finite R D := restrictedCoextensionDual_finite
  exact Module.Finite.of_restrictScalars_finite R S D

end LinearStudy
