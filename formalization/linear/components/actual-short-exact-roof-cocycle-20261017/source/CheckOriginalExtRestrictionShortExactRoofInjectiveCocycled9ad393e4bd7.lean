module
import all Linear.ShortExactRoofInjectiveCocycle
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.shortExactRoof_comp_eq_neg_injectiveCocycle
#print axioms LinearStudy.shortExactRoof_comp_eq_neg_injectiveCocycle
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.shortExactRoof_comp_eq_neg_injectiveCocycle,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
