module
import all Linear.SchemeModuleInternalExtZeroSource
import all Linear.SchemeModuleHomSourceBoundaryCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtZeroIso_source_inv
#print axioms LinearStudy.schemeModuleInternalExtZeroIso_source_inv
#check @LinearStudy.schemeModuleInternalExtZeroIso_source
#print axioms LinearStudy.schemeModuleInternalExtZeroIso_source
#check @LinearStudy.schemeModuleHomSourceBoundaryCokernelIso
#print axioms LinearStudy.schemeModuleHomSourceBoundaryCokernelIso
#check @LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_hom
#print axioms LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_hom
#check @LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_independent
#print axioms LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_independent
#check @LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso
#print axioms LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso
#check @LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso_hom
#print axioms LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso_hom
#print LinearStudy.schemeModuleHomSourceBoundaryCokernelIso
#print LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtZeroIso_source_inv,true),(`LinearStudy.schemeModuleInternalExtZeroIso_source,true),(`LinearStudy.schemeModuleHomSourceBoundaryCokernelIso,false),(`LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_hom,true),(`LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_independent,true),(`LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso,false),(`LinearStudy.schemeModuleFiniteFreeHomSourceCokernelIso_hom,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
