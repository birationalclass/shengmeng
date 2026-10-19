module
import all Linear.NoetherianInjectiveArtinRees
import all Linear.NoetherianInjectiveCompatibleFractions
import all Linear.NoetherianInjectiveStructureSheafSections
import all Linear.NoetherianInjectiveTildeFlasque
import all Linear.PointedExactFunctorExtZeroFullyFaithful
import all Linear.NoetherianAffineActualCohomology
import all Linear.NoetherianAffineQuasicoherentCohomology
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.noetherian_artinRees_kernel_restriction
#print axioms LinearStudy.noetherian_artinRees_kernel_restriction
#check @LinearStudy.injective_linearMap_extend_of_ker_le
#print axioms LinearStudy.injective_linearMap_extend_of_ker_le
#check @LinearStudy.finiteCompatibleFamily_ideal_kills_relations
#print axioms LinearStudy.finiteCompatibleFamily_ideal_kills_relations
#check @LinearStudy.noetherian_injective_compatible_family_lift
#print axioms LinearStudy.noetherian_injective_compatible_family_lift
#check @LinearStudy.noetherian_injective_structureSheaf_toOpen_surjective
#print axioms LinearStudy.noetherian_injective_structureSheaf_toOpen_surjective
#check @LinearStudy.noetherian_injective_tilde_isFlasque
#print axioms LinearStudy.noetherian_injective_tilde_isFlasque
#check @LinearStudy.noetherian_injective_tilde_globalUnitExt_vanish
#print axioms LinearStudy.noetherian_injective_tilde_globalUnitExt_vanish
#check @LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful
#print axioms LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful
#check @LinearStudy.tilde_functor_preservesFiniteLimits
#print axioms LinearStudy.tilde_functor_preservesFiniteLimits
#check @LinearStudy.noetherian_affine_tilde_globalUnitExt_comparison_bijective
#print axioms LinearStudy.noetherian_affine_tilde_globalUnitExt_comparison_bijective
#check @LinearStudy.noetherian_affine_tilde_globalUnitExt_vanish
#print axioms LinearStudy.noetherian_affine_tilde_globalUnitExt_vanish
#check @LinearStudy.noetherian_affine_tilde_actualHigherCohomology_vanish
#print axioms LinearStudy.noetherian_affine_tilde_actualHigherCohomology_vanish
#check @LinearStudy.noetherian_affine_quasicoherent_actualHigherCohomology_vanish
#print axioms LinearStudy.noetherian_affine_quasicoherent_actualHigherCohomology_vanish
#check @LinearStudy.noetherian_affine_quasicoherent_globalUnitExt_vanish
#print axioms LinearStudy.noetherian_affine_quasicoherent_globalUnitExt_vanish
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.noetherian_artinRees_kernel_restriction,true),(`LinearStudy.injective_linearMap_extend_of_ker_le,true),(`LinearStudy.finiteCompatibleFamily_ideal_kills_relations,true),(`LinearStudy.noetherian_injective_compatible_family_lift,true),(`LinearStudy.noetherian_injective_structureSheaf_toOpen_surjective,true),(`LinearStudy.noetherian_injective_tilde_isFlasque,true),(`LinearStudy.noetherian_injective_tilde_globalUnitExt_vanish,true),(`LinearStudy.pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful,true),(`LinearStudy.tilde_functor_preservesFiniteLimits,true),(`LinearStudy.noetherian_affine_tilde_globalUnitExt_comparison_bijective,true),(`LinearStudy.noetherian_affine_tilde_globalUnitExt_vanish,true),(`LinearStudy.noetherian_affine_tilde_actualHigherCohomology_vanish,true),(`LinearStudy.noetherian_affine_quasicoherent_actualHigherCohomology_vanish,true),(`LinearStudy.noetherian_affine_quasicoherent_globalUnitExt_vanish,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
