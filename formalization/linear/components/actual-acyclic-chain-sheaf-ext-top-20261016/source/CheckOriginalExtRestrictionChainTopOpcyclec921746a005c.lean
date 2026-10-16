module
import all Linear.SchemeModuleChainTopOpcycleIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainTopOpcycleIso
#print axioms LinearStudy.schemeModuleChainTopOpcycleIso
#check @LinearStudy.schemeModuleHomSourceIso
#print axioms LinearStudy.schemeModuleHomSourceIso
#check @LinearStudy.schemeModuleChainTopHomCokernelIso
#print axioms LinearStudy.schemeModuleChainTopHomCokernelIso
#check @LinearStudy.schemeModuleChainTopHomCokernelIso_hom
#print axioms LinearStudy.schemeModuleChainTopHomCokernelIso_hom
#print LinearStudy.schemeModuleChainTopOpcycleIso
#print LinearStudy.schemeModuleHomSourceIso
#print LinearStudy.schemeModuleChainTopHomCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainTopOpcycleIso,false),(`LinearStudy.schemeModuleHomSourceIso,false),(`LinearStudy.schemeModuleChainTopHomCokernelIso,false),(`LinearStudy.schemeModuleChainTopHomCokernelIso_hom,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
