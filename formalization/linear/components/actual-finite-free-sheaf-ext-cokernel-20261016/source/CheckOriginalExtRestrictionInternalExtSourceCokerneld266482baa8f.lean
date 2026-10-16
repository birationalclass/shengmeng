module
import all Linear.SchemeModuleInternalExtSourceBoundaryCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_epi
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_epi
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryIsCokernel
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryIsCokernel
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_hom
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_hom
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_independent
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_independent
#check @LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso
#print axioms LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso
#check @LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso_hom
#print axioms LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso_hom
#print LinearStudy.schemeModuleInternalExtSourceBoundaryIsCokernel
#print LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso
#print LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceBoundary_epi,true),(`LinearStudy.schemeModuleInternalExtSourceBoundaryIsCokernel,false),(`LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso,false),(`LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_hom,true),(`LinearStudy.schemeModuleInternalExtSourceBoundaryCokernelIso_independent,true),(`LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso,false),(`LinearStudy.schemeModuleFiniteFreeSourceBoundaryCokernelIso_hom,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
