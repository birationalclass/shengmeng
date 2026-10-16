module
import all Linear.SchemeModuleAcyclicChainTopHomEquation
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_hom_equation
#print axioms LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_hom_equation
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_hom_equation,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
