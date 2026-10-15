module
import all Linear.MappedCochainTopCocycle
import all Linear.OriginalChainMappedTopCocycle
import all Linear.OriginalChainMappedExtComparison
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.mappedCochainResolutionTopCocycle
#print axioms LinearStudy.mappedCochainResolutionTopCocycle
#check @LinearStudy.mappedOriginalChainTopCocycle
#print axioms LinearStudy.mappedOriginalChainTopCocycle
#check @LinearStudy.mappedOriginalChainAugmentation_quasiIso
#print axioms LinearStudy.mappedOriginalChainAugmentation_quasiIso
#check @LinearStudy.originalChainMappedTopExtClass_eq_mappedChain
#print axioms LinearStudy.originalChainMappedTopExtClass_eq_mappedChain
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.mappedCochainResolutionTopCocycle,true),(`LinearStudy.mappedOriginalChainTopCocycle,true),(`LinearStudy.mappedOriginalChainAugmentation_quasiIso,true),(`LinearStudy.originalChainMappedTopExtClass_eq_mappedChain,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
