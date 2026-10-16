module
import all Linear.SchemeModuleChainOpcycleExtShift
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleExtShiftIso
#print axioms LinearStudy.schemeModuleChainOpcycleExtShiftIso
#check @LinearStudy.schemeModuleChainOpcycleExtShiftIso_hom
#print axioms LinearStudy.schemeModuleChainOpcycleExtShiftIso_hom
#check @LinearStudy.schemeModuleChainOpcycleHomCokernelIso
#print axioms LinearStudy.schemeModuleChainOpcycleHomCokernelIso
#check @LinearStudy.schemeModuleChainOpcycleIteratedExtIso
#print axioms LinearStudy.schemeModuleChainOpcycleIteratedExtIso
#check @LinearStudy.schemeModuleChainOpcycleExtCokernelIso
#print axioms LinearStudy.schemeModuleChainOpcycleExtCokernelIso
#print LinearStudy.schemeModuleChainOpcycleExtShiftIso
#print LinearStudy.schemeModuleChainOpcycleHomCokernelIso
#print LinearStudy.schemeModuleChainOpcycleIteratedExtIso
#print LinearStudy.schemeModuleChainOpcycleExtCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleExtShiftIso,false),(`LinearStudy.schemeModuleChainOpcycleExtShiftIso_hom,true),(`LinearStudy.schemeModuleChainOpcycleHomCokernelIso,false),(`LinearStudy.schemeModuleChainOpcycleIteratedExtIso,false),(`LinearStudy.schemeModuleChainOpcycleExtCokernelIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
