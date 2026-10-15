module
import all Linear.AdditiveFunctorExtendComplex
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.additiveFunctorExtendXIso
#print axioms LinearStudy.additiveFunctorExtendXIso
#check @LinearStudy.additiveFunctorExtendXIso_comm
#print axioms LinearStudy.additiveFunctorExtendXIso_comm
#check @LinearStudy.additiveFunctorExtendComplexIso
#print axioms LinearStudy.additiveFunctorExtendComplexIso
#print LinearStudy.additiveFunctorExtendXIso
#print LinearStudy.additiveFunctorExtendComplexIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.additiveFunctorExtendXIso,false),(`LinearStudy.additiveFunctorExtendXIso_comm,true),(`LinearStudy.additiveFunctorExtendComplexIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
