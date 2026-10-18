module
import all Linear.SchemeModuleOpenKoszulDataFromMappedPresentation
import all Linear.SchemeModuleOpenKoszulDataSourceEq
import all Linear.NativeKoszulMappedChartComplexIdentity
import all Linear.NativeProjectiveOpenKoszulExactChart
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOpenKoszulChartData_of_mappedPresentation
#print axioms LinearStudy.schemeModuleOpenKoszulChartData_of_mappedPresentation
#check @LinearStudy.schemeModuleOpenKoszulChartData_of_sourceIdentification
#print axioms LinearStudy.schemeModuleOpenKoszulChartData_of_sourceIdentification
#check @LinearStudy.nativeKoszulMappedChartComplex_identity
#print axioms LinearStudy.nativeKoszulMappedChartComplex_identity
#check @LinearStudy.nativeProjectiveOpenKoszulExactChart
#print axioms LinearStudy.nativeProjectiveOpenKoszulExactChart
#print LinearStudy.schemeModuleOpenKoszulChartData_of_mappedPresentation
#print LinearStudy.schemeModuleOpenKoszulChartData_of_sourceIdentification
#print LinearStudy.nativeProjectiveOpenKoszulExactChart
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOpenKoszulChartData_of_mappedPresentation,false),(`LinearStudy.schemeModuleOpenKoszulChartData_of_sourceIdentification,false),(`LinearStudy.nativeKoszulMappedChartComplex_identity,true),(`LinearStudy.nativeProjectiveOpenKoszulExactChart,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
