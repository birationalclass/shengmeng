module
import all Linear.CochainShortExactRoofClass
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainShortExactRoofClass
#print axioms LinearStudy.cochainShortExactRoofClass
#check @LinearStudy.cochainShortExactRoofClass_eq_extClass
#print axioms LinearStudy.cochainShortExactRoofClass_eq_extClass
#check @LinearStudy.cochainShortExactRoofClass_contravariant_zero_sign
#print axioms LinearStudy.cochainShortExactRoofClass_contravariant_zero_sign
#print LinearStudy.cochainShortExactRoofClass
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainShortExactRoofClass,false),(`LinearStudy.cochainShortExactRoofClass_eq_extClass,true),(`LinearStudy.cochainShortExactRoofClass_contravariant_zero_sign,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
