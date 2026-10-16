module
import all Linear.CochainSingleSupportComponents
import all Linear.CochainAugmentedTopHomotopyComponents
import all Linear.CochainResolutionTopHomotopyEquations
import all Linear.CochainSourceLiftSigns
import all Linear.CochainResolutionSourceLiftEquations
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainSingleAugmentation_precomp_v_zero
#print axioms LinearStudy.cochainSingleAugmentation_precomp_v_zero
#check @LinearStudy.cochainTopFunctional_postcomp_v_zero
#print axioms LinearStudy.cochainTopFunctional_postcomp_v_zero
#check @LinearStudy.cochainAugmentedTopHomotopy_middle
#print axioms LinearStudy.cochainAugmentedTopHomotopy_middle
#check @LinearStudy.cochainAugmentedTopHomotopy_top
#print axioms LinearStudy.cochainAugmentedTopHomotopy_top
#check @LinearStudy.cochainAugmentedTopHomotopy_bottom
#print axioms LinearStudy.cochainAugmentedTopHomotopy_bottom
#check @LinearStudy.cochainResolutionTopHomotopyEquations_exists
#print axioms LinearStudy.cochainResolutionTopHomotopyEquations_exists
#check @LinearStudy.cochainSourceLiftSigns
#print axioms LinearStudy.cochainSourceLiftSigns
#check @LinearStudy.cochainSourceLiftSigns_top
#print axioms LinearStudy.cochainSourceLiftSigns_top
#check @LinearStudy.cochainSourceLiftSigns_middle
#print axioms LinearStudy.cochainSourceLiftSigns_middle
#check @LinearStudy.cochainSourceLiftSigns_bottom
#print axioms LinearStudy.cochainSourceLiftSigns_bottom
#check @LinearStudy.cochainResolutionSourceLiftEquations_exists
#print axioms LinearStudy.cochainResolutionSourceLiftEquations_exists
#print LinearStudy.cochainSourceLiftSigns
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainSingleAugmentation_precomp_v_zero,true),(`LinearStudy.cochainTopFunctional_postcomp_v_zero,true),(`LinearStudy.cochainAugmentedTopHomotopy_middle,true),(`LinearStudy.cochainAugmentedTopHomotopy_top,true),(`LinearStudy.cochainAugmentedTopHomotopy_bottom,true),(`LinearStudy.cochainResolutionTopHomotopyEquations_exists,true),(`LinearStudy.cochainSourceLiftSigns,false),(`LinearStudy.cochainSourceLiftSigns_top,true),(`LinearStudy.cochainSourceLiftSigns_middle,true),(`LinearStudy.cochainSourceLiftSigns_bottom,true),(`LinearStudy.cochainResolutionSourceLiftEquations_exists,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
