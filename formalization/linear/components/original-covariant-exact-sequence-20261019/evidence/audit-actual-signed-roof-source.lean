module
import all Linear.CochainOpcycleSignedRoof
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainTopOpcycleFunctional_projection
#print axioms LinearStudy.cochainTopOpcycleFunctional_projection
#check @LinearStudy.cochainOpcycleSignedExtension_eq_actual_roof
#print axioms LinearStudy.cochainOpcycleSignedExtension_eq_actual_roof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainTopOpcycleFunctional_projection,true),(`LinearStudy.cochainOpcycleSignedExtension_eq_actual_roof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
