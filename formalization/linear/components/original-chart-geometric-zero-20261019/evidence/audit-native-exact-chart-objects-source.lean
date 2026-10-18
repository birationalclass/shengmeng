module
import all Linear.NativeProjectiveOpenKoszulExactChartObjects
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeProjectiveOpenKoszulExactChart_ring
#print axioms LinearStudy.nativeProjectiveOpenKoszulExactChart_ring
#check @LinearStudy.nativeProjectiveOpenKoszulExactChart_inclusion
#print axioms LinearStudy.nativeProjectiveOpenKoszulExactChart_inclusion
#check @LinearStudy.nativeProjectiveOpenKoszulExactChart_equations
#print axioms LinearStudy.nativeProjectiveOpenKoszulExactChart_equations
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeProjectiveOpenKoszulExactChart_ring,true),(`LinearStudy.nativeProjectiveOpenKoszulExactChart_inclusion,true),(`LinearStudy.nativeProjectiveOpenKoszulExactChart_equations,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
