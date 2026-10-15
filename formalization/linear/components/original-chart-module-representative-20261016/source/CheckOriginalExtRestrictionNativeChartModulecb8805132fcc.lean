module
import all Linear.NativeProjectiveKoszulChartModuleExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeProjectiveKoszulChartModuleExtLaw
#print axioms LinearStudy.nativeProjectiveKoszulChartModuleExtLaw
#check @LinearStudy.nativeProjectiveKoszulChartModuleExtLaw_proof
#print axioms LinearStudy.nativeProjectiveKoszulChartModuleExtLaw_proof
#print LinearStudy.nativeProjectiveKoszulChartModuleExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeProjectiveKoszulChartModuleExtLaw,false),(`LinearStudy.nativeProjectiveKoszulChartModuleExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
