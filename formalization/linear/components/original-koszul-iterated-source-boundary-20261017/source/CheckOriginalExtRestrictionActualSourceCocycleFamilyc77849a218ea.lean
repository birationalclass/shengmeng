module
import all Linear.CochainSourceLiftFamily
import all Linear.CochainSourceLiftRecurrence
import all Linear.CochainSourceLiftComponentRecurrence
import all Linear.CochainSourceLiftClasses
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainSourceLiftMorph
#print axioms LinearStudy.cochainSourceLiftMorph
#check @LinearStudy.cochainSourceLiftMorph_lt
#print axioms LinearStudy.cochainSourceLiftMorph_lt
#check @LinearStudy.cochainSourceLiftMorph_last
#print axioms LinearStudy.cochainSourceLiftMorph_last
#check @LinearStudy.cochainSourceLiftRecurrence
#print axioms LinearStudy.cochainSourceLiftRecurrence
#check @LinearStudy.cochainSourceLiftMorph_closed
#print axioms LinearStudy.cochainSourceLiftMorph_closed
#check @LinearStudy.cochainSourceTerminalMorph
#print axioms LinearStudy.cochainSourceTerminalMorph
#check @LinearStudy.cochainSourceLiftRecurrence_of_components
#print axioms LinearStudy.cochainSourceLiftRecurrence_of_components
#check @LinearStudy.cochainSourceLiftClass
#print axioms LinearStudy.cochainSourceLiftClass
#check @LinearStudy.cochainSourceLiftClass_boundary
#print axioms LinearStudy.cochainSourceLiftClass_boundary
#check @LinearStudy.cochainSourceLiftClass_iterated
#print axioms LinearStudy.cochainSourceLiftClass_iterated
#print LinearStudy.cochainSourceLiftMorph
#print LinearStudy.cochainSourceLiftRecurrence
#print LinearStudy.cochainSourceTerminalMorph
#print LinearStudy.cochainSourceLiftClass
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainSourceLiftMorph,false),(`LinearStudy.cochainSourceLiftMorph_lt,true),(`LinearStudy.cochainSourceLiftMorph_last,true),(`LinearStudy.cochainSourceLiftRecurrence,false),(`LinearStudy.cochainSourceLiftMorph_closed,true),(`LinearStudy.cochainSourceTerminalMorph,false),(`LinearStudy.cochainSourceLiftRecurrence_of_components,true),(`LinearStudy.cochainSourceLiftClass,false),(`LinearStudy.cochainSourceLiftClass_boundary,true),(`LinearStudy.cochainSourceLiftClass_iterated,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
