module
import all Linear.SchemeModuleHomArrowCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomArrowCokernelIso
#print axioms LinearStudy.schemeModuleHomArrowCokernelIso
#check @LinearStudy.schemeModuleHomArrowCokernelIso_projection
#print axioms LinearStudy.schemeModuleHomArrowCokernelIso_projection
#check @LinearStudy.schemeModuleHomArrowCokernelIso_class
#print axioms LinearStudy.schemeModuleHomArrowCokernelIso_class
#print LinearStudy.schemeModuleHomArrowCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomArrowCokernelIso,false),(`LinearStudy.schemeModuleHomArrowCokernelIso_projection,true),(`LinearStudy.schemeModuleHomArrowCokernelIso_class,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
