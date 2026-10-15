module
import all Linear.SchemeModuleHomPostcompose
import all Linear.SchemeModuleInternalHomCoefficientFunctor
import all Linear.SchemeModuleInternalHomCoefficientLimits
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomPostcompose
#print axioms LinearStudy.schemeModuleHomPostcompose
#check @LinearStudy.schemeModuleHomPostcompose_app
#print axioms LinearStudy.schemeModuleHomPostcompose_app
#check @LinearStudy.schemeModuleHomPostcompose_id
#print axioms LinearStudy.schemeModuleHomPostcompose_id
#check @LinearStudy.schemeModuleHomPostcompose_comp
#print axioms LinearStudy.schemeModuleHomPostcompose_comp
#check @LinearStudy.schemeModuleHomPostcompose_add
#print axioms LinearStudy.schemeModuleHomPostcompose_add
#check @LinearStudy.schemeModuleInternalHomCoefficientFunctor
#print axioms LinearStudy.schemeModuleInternalHomCoefficientFunctor
#check @LinearStudy.schemeModuleInternalHomCoefficientFunctor_map_app
#print axioms LinearStudy.schemeModuleInternalHomCoefficientFunctor_map_app
#check @LinearStudy.schemeModuleInternalHomCoefficientFunctor_additive
#print axioms LinearStudy.schemeModuleInternalHomCoefficientFunctor_additive
#check @LinearStudy.schemeModuleInternalHomCoefficientSectionIso
#print axioms LinearStudy.schemeModuleInternalHomCoefficientSectionIso
#check @LinearStudy.schemeModuleOverFunctor_preservesFiniteLimits
#print axioms LinearStudy.schemeModuleOverFunctor_preservesFiniteLimits
#check @LinearStudy.schemeModuleInternalHomCoefficientFunctor_preservesFiniteLimits
#print axioms LinearStudy.schemeModuleInternalHomCoefficientFunctor_preservesFiniteLimits
#print LinearStudy.schemeModuleHomPostcompose
#print LinearStudy.schemeModuleInternalHomCoefficientFunctor
#print LinearStudy.schemeModuleInternalHomCoefficientFunctor_additive
#print LinearStudy.schemeModuleInternalHomCoefficientSectionIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomPostcompose,false),(`LinearStudy.schemeModuleHomPostcompose_app,true),(`LinearStudy.schemeModuleHomPostcompose_id,true),(`LinearStudy.schemeModuleHomPostcompose_comp,true),(`LinearStudy.schemeModuleHomPostcompose_add,true),(`LinearStudy.schemeModuleInternalHomCoefficientFunctor,false),(`LinearStudy.schemeModuleInternalHomCoefficientFunctor_map_app,true),(`LinearStudy.schemeModuleInternalHomCoefficientFunctor_additive,true),(`LinearStudy.schemeModuleInternalHomCoefficientSectionIso,false),(`LinearStudy.schemeModuleOverFunctor_preservesFiniteLimits,true),(`LinearStudy.schemeModuleInternalHomCoefficientFunctor_preservesFiniteLimits,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
