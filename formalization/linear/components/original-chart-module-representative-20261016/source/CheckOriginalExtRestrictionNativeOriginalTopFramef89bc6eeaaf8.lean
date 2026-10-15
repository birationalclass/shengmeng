module
import all Linear.NativeProjectiveKoszulTopModuleFrame
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeProjectiveKoszulTopChartModuleFrame
#print axioms LinearStudy.nativeProjectiveKoszulTopChartModuleFrame
#check @LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw
#print axioms LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw
#check @LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw_proof
#print axioms LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw_proof
#print LinearStudy.nativeProjectiveKoszulTopChartModuleFrame
#print LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeProjectiveKoszulTopChartModuleFrame,false),(`LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw,false),(`LinearStudy.nativeProjectiveKoszulTopChartModuleFrameLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
