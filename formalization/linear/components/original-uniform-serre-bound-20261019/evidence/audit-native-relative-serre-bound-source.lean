module
import all Linear.NativeKoszulRelativeExtSerreBound
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeKoszulRelativeExt_term_of_twist_bound
#print axioms LinearStudy.nativeKoszulRelativeExt_term_of_twist_bound
#check @LinearStudy.nativeKoszulRelativeExt_middle_of_Serre_bound
#print axioms LinearStudy.nativeKoszulRelativeExt_middle_of_Serre_bound
#check @LinearStudy.nativeKoszulRelativeExt_uniform_bound
#print axioms LinearStudy.nativeKoszulRelativeExt_uniform_bound
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeKoszulRelativeExt_term_of_twist_bound,true),(`LinearStudy.nativeKoszulRelativeExt_middle_of_Serre_bound,true),(`LinearStudy.nativeKoszulRelativeExt_uniform_bound,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
