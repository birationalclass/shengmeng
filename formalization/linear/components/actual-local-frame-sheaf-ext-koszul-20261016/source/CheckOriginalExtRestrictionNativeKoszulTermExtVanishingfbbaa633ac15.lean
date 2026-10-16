module
import all Linear.NativeProjectiveKoszulTermInternalExtVanishing
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeProjectiveKoszulTermInternalExt_succ
#print axioms LinearStudy.nativeProjectiveKoszulTermInternalExt_succ
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeProjectiveKoszulTermInternalExt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
