module
import all Linear.SchemeModuleHomZeroSourceSupport
import all Linear.SchemeModuleSupportedSubHomFlasque
import all Linear.SchemeModulePushforwardOpenSupport
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomModuleSheaf_isZero_of_source
#print axioms LinearStudy.schemeModuleHomModuleSheaf_isZero_of_source
#check @LinearStudy.schemeModuleHomModuleSheaf_open_isZero_of_source
#print axioms LinearStudy.schemeModuleHomModuleSheaf_open_isZero_of_source
#check @LinearStudy.schemeModuleSubHom_open_isZero_of_source
#print axioms LinearStudy.schemeModuleSubHom_open_isZero_of_source
#check @LinearStudy.schemeModuleSubHom_supportedFlasque
#print axioms LinearStudy.schemeModuleSubHom_supportedFlasque
#check @LinearStudy.schemeModuleSubHom_closedDiscreteFlasque
#print axioms LinearStudy.schemeModuleSubHom_closedDiscreteFlasque
#check @LinearStudy.schemeModulePushforward_sections_subsingleton_of_disjointRange
#print axioms LinearStudy.schemeModulePushforward_sections_subsingleton_of_disjointRange
#check @LinearStudy.schemeModulePushforward_open_isZero_of_disjointRange
#print axioms LinearStudy.schemeModulePushforward_open_isZero_of_disjointRange
#check @LinearStudy.schemeModuleSubHom_pushforward_closedDiscreteFlasque
#print axioms LinearStudy.schemeModuleSubHom_pushforward_closedDiscreteFlasque
#check @LinearStudy.schemeModuleSubHom_artinianClosedImmersionFlasque
#print axioms LinearStudy.schemeModuleSubHom_artinianClosedImmersionFlasque
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomModuleSheaf_isZero_of_source,true),(`LinearStudy.schemeModuleHomModuleSheaf_open_isZero_of_source,true),(`LinearStudy.schemeModuleSubHom_open_isZero_of_source,true),(`LinearStudy.schemeModuleSubHom_supportedFlasque,true),(`LinearStudy.schemeModuleSubHom_closedDiscreteFlasque,true),(`LinearStudy.schemeModulePushforward_sections_subsingleton_of_disjointRange,true),(`LinearStudy.schemeModulePushforward_open_isZero_of_disjointRange,true),(`LinearStudy.schemeModuleSubHom_pushforward_closedDiscreteFlasque,true),(`LinearStudy.schemeModuleSubHom_artinianClosedImmersionFlasque,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
