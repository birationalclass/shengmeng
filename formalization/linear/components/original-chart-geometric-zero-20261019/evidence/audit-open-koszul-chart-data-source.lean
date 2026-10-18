module
import all Linear.SchemeModuleOpenKoszulChartData
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOpenKoszulChartData
#print axioms LinearStudy.schemeModuleOpenKoszulChartData
#check @LinearStudy.schemeModuleOpenKoszulChartDataCutStatement
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataCutStatement
#check @LinearStudy.schemeModuleOpenKoszulChartDataCutStatement_proof
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataCutStatement_proof
#print LinearStudy.schemeModuleOpenKoszulChartData
#print LinearStudy.schemeModuleOpenKoszulChartDataCutStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOpenKoszulChartData,false),(`LinearStudy.schemeModuleOpenKoszulChartDataCutStatement,false),(`LinearStudy.schemeModuleOpenKoszulChartDataCutStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
