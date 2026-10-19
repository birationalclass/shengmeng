module
import all Linear.NativeKoszulCovariantSerreBound
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement
#print axioms LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement
#check @LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement_of_Serre
#print axioms LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement_of_Serre
#check @LinearStudy.nativeKoszul_uniformCovariantExact_from_Serre
#print axioms LinearStudy.nativeKoszul_uniformCovariantExact_from_Serre
#print LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement,false),(`LinearStudy.nativeKoszulCovariantAtOriginalTwistStatement_of_Serre,true),(`LinearStudy.nativeKoszul_uniformCovariantExact_from_Serre,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
