module
import all Linear.SchemeModuleAcyclicChainExtIndependence
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleExtShiftIso_independent
#print axioms LinearStudy.schemeModuleChainOpcycleExtShiftIso_independent
#check @LinearStudy.schemeModuleChainOpcycleHomCokernelIso_independent
#print axioms LinearStudy.schemeModuleChainOpcycleHomCokernelIso_independent
#check @LinearStudy.schemeModuleChainOpcycleIteratedExtIso_independent
#print axioms LinearStudy.schemeModuleChainOpcycleIteratedExtIso_independent
#check @LinearStudy.schemeModuleChainOpcycleExtCokernelIso_independent
#print axioms LinearStudy.schemeModuleChainOpcycleExtCokernelIso_independent
#check @LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_independent
#print axioms LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_independent
#check @LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_independent
#print axioms LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_independent
#check @LinearStudy.schemeModuleAcyclicCokernelRankInternalExtIso_independent
#print axioms LinearStudy.schemeModuleAcyclicCokernelRankInternalExtIso_independent
#check @LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution
#print axioms LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleExtShiftIso_independent,true),(`LinearStudy.schemeModuleChainOpcycleHomCokernelIso_independent,true),(`LinearStudy.schemeModuleChainOpcycleIteratedExtIso_independent,true),(`LinearStudy.schemeModuleChainOpcycleExtCokernelIso_independent,true),(`LinearStudy.schemeModuleAcyclicChainTopInternalExtIso_independent,true),(`LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_independent,true),(`LinearStudy.schemeModuleAcyclicCokernelRankInternalExtIso_independent,true),(`LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_eq_viaResolution,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
