module
import all Linear.NativeIntegerTwistInternalExtVanishing
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeIntegerTwistInternalExt_succ
#print axioms LinearStudy.nativeIntegerTwistInternalExt_succ
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeIntegerTwistInternalExt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
