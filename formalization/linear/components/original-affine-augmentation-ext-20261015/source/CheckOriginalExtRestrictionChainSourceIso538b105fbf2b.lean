module
import all Linear.OriginalChainTopExtSourceIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainAugmentationAsCochain_sourceIso
#print axioms LinearStudy.originalChainAugmentationAsCochain_sourceIso
#check @LinearStudy.originalChainTopShiftedCocycle_sourceIso
#print axioms LinearStudy.originalChainTopShiftedCocycle_sourceIso
#check @LinearStudy.originalChainTopExtClass_sourceIso
#print axioms LinearStudy.originalChainTopExtClass_sourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainAugmentationAsCochain_sourceIso,true),(`LinearStudy.originalChainTopShiftedCocycle_sourceIso,true),(`LinearStudy.originalChainTopExtClass_sourceIso,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
