module
import all Linear.SchemeModuleChainOpcycleSequence
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleSequence
#print axioms LinearStudy.schemeModuleChainOpcycleSequence
#check @LinearStudy.schemeModuleChainOpcycleSequenceIsCokernel
#print axioms LinearStudy.schemeModuleChainOpcycleSequenceIsCokernel
#check @LinearStudy.schemeModuleChainOpcycleSequence_shortExact
#print axioms LinearStudy.schemeModuleChainOpcycleSequence_shortExact
#print LinearStudy.schemeModuleChainOpcycleSequence
#print LinearStudy.schemeModuleChainOpcycleSequenceIsCokernel
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleSequence,false),(`LinearStudy.schemeModuleChainOpcycleSequenceIsCokernel,false),(`LinearStudy.schemeModuleChainOpcycleSequence_shortExact,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
