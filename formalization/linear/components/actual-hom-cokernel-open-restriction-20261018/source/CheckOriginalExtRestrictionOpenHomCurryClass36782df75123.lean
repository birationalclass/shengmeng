module
import all Linear.SchemeModuleHomOpenImmersionCurry
import all Linear.SchemeModuleHomOpenImmersionCokernelClass
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomOpenImmersionIso_curry
#print axioms LinearStudy.schemeModuleHomOpenImmersionIso_curry
#check @LinearStudy.schemeModuleHomOpenImmersionCokernelIso_class
#print axioms LinearStudy.schemeModuleHomOpenImmersionCokernelIso_class
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomOpenImmersionIso_curry,true),(`LinearStudy.schemeModuleHomOpenImmersionCokernelIso_class,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
