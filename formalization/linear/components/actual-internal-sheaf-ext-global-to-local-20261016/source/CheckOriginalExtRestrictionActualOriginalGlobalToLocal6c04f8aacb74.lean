module
import all Linear.SchemeModuleOriginalClassGlobalToLocal
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalChainTopExtClassSmall
#print axioms LinearStudy.schemeModuleOriginalChainTopExtClassSmall
#check @LinearStudy.schemeModuleOriginalChainTopExtClassSmall_comp_mk₀
#print axioms LinearStudy.schemeModuleOriginalChainTopExtClassSmall_comp_mk₀
#check @LinearStudy.schemeModuleOriginalChainClass_globalToLocal_coefficient
#print axioms LinearStudy.schemeModuleOriginalChainClass_globalToLocal_coefficient
#print LinearStudy.schemeModuleOriginalChainTopExtClassSmall
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalChainTopExtClassSmall,false),(`LinearStudy.schemeModuleOriginalChainTopExtClassSmall_comp_mk₀,true),(`LinearStudy.schemeModuleOriginalChainClass_globalToLocal_coefficient,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
