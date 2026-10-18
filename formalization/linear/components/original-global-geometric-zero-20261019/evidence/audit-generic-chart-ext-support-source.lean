module
import all Linear.SchemeModuleChartInternalExtSupport
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChartInternalExtSupportStatement
#print axioms LinearStudy.schemeModuleChartInternalExtSupportStatement
#check @LinearStudy.schemeModuleChartInternalExtSupportStatement_of_chartHEq
#print axioms LinearStudy.schemeModuleChartInternalExtSupportStatement_of_chartHEq
#print LinearStudy.schemeModuleChartInternalExtSupportStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChartInternalExtSupportStatement,false),(`LinearStudy.schemeModuleChartInternalExtSupportStatement_of_chartHEq,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
