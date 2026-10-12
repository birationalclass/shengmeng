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

/-- The original finite coextension dual is finite over the original
upper ring as well as its normalization base. The upper action is the
native coextension action, without an extra module-finiteness input. -/
theorem nativeCoextensionDual_finite_upper [IsNoetherianRing R] [Module.Finite R S] :
    Module.Finite S
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let : Module R D := Module.compHom D (algebraMap R S)
  let : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  let : Module.Finite R D := restrictedCoextensionDual_finite (R := R) (S := S)
  exact Module.Finite.of_restrictScalars_finite R S D

end LinearStudy
