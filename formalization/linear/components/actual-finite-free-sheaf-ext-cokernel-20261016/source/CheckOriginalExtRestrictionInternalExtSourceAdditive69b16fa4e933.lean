module
import all Linear.SchemeModuleInternalExtSourceAdditive
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomCoefficientComplexMap_add
#print axioms LinearStudy.schemeModuleHomCoefficientComplexMap_add
#check @LinearStudy.schemeModuleInternalExtSourceMap_add
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_add
#check @LinearStudy.schemeModuleInternalExtSourceFunctor
#print axioms LinearStudy.schemeModuleInternalExtSourceFunctor
#check @LinearStudy.schemeModuleInternalExtSourceFunctor_additive
#print axioms LinearStudy.schemeModuleInternalExtSourceFunctor_additive
#print LinearStudy.schemeModuleInternalExtSourceFunctor
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomCoefficientComplexMap_add,true),(`LinearStudy.schemeModuleInternalExtSourceMap_add,true),(`LinearStudy.schemeModuleInternalExtSourceFunctor,false),(`LinearStudy.schemeModuleInternalExtSourceFunctor_additive,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
