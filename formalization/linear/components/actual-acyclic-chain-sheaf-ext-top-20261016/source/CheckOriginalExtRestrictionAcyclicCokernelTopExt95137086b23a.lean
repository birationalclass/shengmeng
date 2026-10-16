module
import all Linear.SchemeModuleAcyclicCokernelTopInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleZeroCokernelIso
#print axioms LinearStudy.schemeModuleChainOpcycleZeroCokernelIso
#check @LinearStudy.schemeModuleChainOpcycleZeroCokernelIso_projection
#print axioms LinearStudy.schemeModuleChainOpcycleZeroCokernelIso_projection
#check @LinearStudy.schemeModuleCokernelAugmentation_exactAt_succ
#print axioms LinearStudy.schemeModuleCokernelAugmentation_exactAt_succ
#check @LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso
#print axioms LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso
#print LinearStudy.schemeModuleChainOpcycleZeroCokernelIso
#print LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleZeroCokernelIso,false),(`LinearStudy.schemeModuleChainOpcycleZeroCokernelIso_projection,true),(`LinearStudy.schemeModuleCokernelAugmentation_exactAt_succ,true),(`LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
