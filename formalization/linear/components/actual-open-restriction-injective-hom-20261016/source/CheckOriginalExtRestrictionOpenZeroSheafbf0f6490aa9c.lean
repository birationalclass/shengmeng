module
import all Linear.OverOpenZeroSheafFunctor
import all Linear.OverOpenZeroSheafAdjunction
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.overOpenZeroSheafFunctor
#print axioms LinearStudy.overOpenZeroSheafFunctor
#check @LinearStudy.overOpenZeroSheafFunctor_preservesMonomorphisms
#print axioms LinearStudy.overOpenZeroSheafFunctor_preservesMonomorphisms
#check @LinearStudy.overOpenZeroPresheafSheafificationAdjunction
#print axioms LinearStudy.overOpenZeroPresheafSheafificationAdjunction
#check @LinearStudy.overOpenZeroSheafHomEquiv
#print axioms LinearStudy.overOpenZeroSheafHomEquiv
#check @LinearStudy.overOpenZeroSheafAdjunction
#print axioms LinearStudy.overOpenZeroSheafAdjunction
#print LinearStudy.overOpenZeroSheafFunctor
#print LinearStudy.overOpenZeroPresheafSheafificationAdjunction
#print LinearStudy.overOpenZeroSheafHomEquiv
#print LinearStudy.overOpenZeroSheafAdjunction
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.overOpenZeroSheafFunctor,false),(`LinearStudy.overOpenZeroSheafFunctor_preservesMonomorphisms,true),(`LinearStudy.overOpenZeroPresheafSheafificationAdjunction,false),(`LinearStudy.overOpenZeroSheafHomEquiv,false),(`LinearStudy.overOpenZeroSheafAdjunction,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
