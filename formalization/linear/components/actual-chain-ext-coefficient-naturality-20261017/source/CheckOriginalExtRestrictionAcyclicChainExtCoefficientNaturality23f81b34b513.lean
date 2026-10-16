module
import all Linear.SchemeModuleAcyclicChainExtCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleAcyclicCokernelRankInternalExtNatIso
#print axioms LinearStudy.schemeModuleAcyclicCokernelRankInternalExtNatIso
#print LinearStudy.schemeModuleAcyclicCokernelRankInternalExtNatIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleAcyclicCokernelRankInternalExtNatIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
