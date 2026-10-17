module
import all Linear.SchemeModuleHomOpenImmersionCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomOpenImmersionCokernelIso
#print axioms LinearStudy.schemeModuleHomOpenImmersionCokernelIso
#check @LinearStudy.schemeModuleHomOpenImmersionCokernelIso_projection
#print axioms LinearStudy.schemeModuleHomOpenImmersionCokernelIso_projection
#print LinearStudy.schemeModuleHomOpenImmersionCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomOpenImmersionCokernelIso,false),(`LinearStudy.schemeModuleHomOpenImmersionCokernelIso_projection,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
