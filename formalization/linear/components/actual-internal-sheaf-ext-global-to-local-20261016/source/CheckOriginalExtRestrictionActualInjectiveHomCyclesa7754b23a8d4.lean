module
import all Linear.SchemeModuleInjectiveInternalHomCycles
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHomComplex
#print axioms LinearStudy.schemeModuleInjectiveInternalHomComplex
#check @LinearStudy.schemeModuleInjectiveInternalHomCycleMap
#print axioms LinearStudy.schemeModuleInjectiveInternalHomCycleMap
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary_zero
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary_zero
#print LinearStudy.schemeModuleInjectiveInternalHomComplex
#print LinearStudy.schemeModuleInjectiveInternalHomCycleMap
#print LinearStudy.schemeModuleInjectiveInternalHomClassMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHomComplex,false),(`LinearStudy.schemeModuleInjectiveInternalHomCycleMap,false),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap,false),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary_zero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
