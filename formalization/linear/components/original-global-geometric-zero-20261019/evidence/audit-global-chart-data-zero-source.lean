module
import all Linear.SchemeModuleOpenKoszulChartDataGlobalZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroStatement
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroStatement
#check @LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof
#print LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroStatement,false),(`LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
