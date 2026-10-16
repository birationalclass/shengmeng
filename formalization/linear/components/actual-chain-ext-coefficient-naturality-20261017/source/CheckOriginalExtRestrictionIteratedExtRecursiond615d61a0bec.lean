module
import all Linear.SchemeModuleIteratedExtRecursion
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleIteratedExtIso_zero
#print axioms LinearStudy.schemeModuleChainOpcycleIteratedExtIso_zero
#check @LinearStudy.schemeModuleChainOpcycleIteratedExtIso_succ
#print axioms LinearStudy.schemeModuleChainOpcycleIteratedExtIso_succ
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleIteratedExtIso_zero,true),(`LinearStudy.schemeModuleChainOpcycleIteratedExtIso_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
