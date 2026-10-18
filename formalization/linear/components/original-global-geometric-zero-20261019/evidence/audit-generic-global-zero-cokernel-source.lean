module
import all Linear.SchemeModuleGlobalGeometricZeroCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof_of_cokernelLambda
#print axioms LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof_of_cokernelLambda
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOpenKoszulChartDataGlobalZeroProof_of_cokernelLambda,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
