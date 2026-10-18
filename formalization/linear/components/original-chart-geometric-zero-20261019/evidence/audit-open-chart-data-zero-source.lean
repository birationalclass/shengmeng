module
import all Linear.SchemeModuleOpenKoszulChartDataCutZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOpenKoszulChartDataCutZeroStatement
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataCutZeroStatement
#check @LinearStudy.schemeModuleOpenKoszulChartDataCutZeroProof
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataCutZeroProof
#print LinearStudy.schemeModuleOpenKoszulChartDataCutZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOpenKoszulChartDataCutZeroStatement,false),(`LinearStudy.schemeModuleOpenKoszulChartDataCutZeroProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
