module
import all Linear.OriginalChainOpcycleEmbedding
import all Linear.SchemeModuleOriginalOpcycleSourceIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainAsCochainOpcyclesIso
#print axioms LinearStudy.originalChainAsCochainOpcyclesIso
#check @LinearStudy.originalChainAsCochain_pOpcycles
#print axioms LinearStudy.originalChainAsCochain_pOpcycles
#check @LinearStudy.originalChainAsCochain_fromOpcycles
#print axioms LinearStudy.originalChainAsCochain_fromOpcycles
#check @LinearStudy.schemeModuleOriginalOpcycleSourceIso
#print axioms LinearStudy.schemeModuleOriginalOpcycleSourceIso
#check @LinearStudy.originalChainAugmentation_exactAt_succ
#print axioms LinearStudy.originalChainAugmentation_exactAt_succ
#print LinearStudy.originalChainAsCochainOpcyclesIso
#print LinearStudy.schemeModuleOriginalOpcycleSourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainAsCochainOpcyclesIso,false),(`LinearStudy.originalChainAsCochain_pOpcycles,true),(`LinearStudy.originalChainAsCochain_fromOpcycles,true),(`LinearStudy.schemeModuleOriginalOpcycleSourceIso,false),(`LinearStudy.originalChainAugmentation_exactAt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
