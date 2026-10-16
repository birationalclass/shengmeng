module
import all Linear.InjectiveCochainCocycleSourceClass
import all Linear.CochainCocycleOfHomShifted
import all Linear.InjectiveCochainDegreeZeroClass
import all Linear.CochainSourceLiftInitialClass
import all Linear.CochainSourceLiftTerminalClass
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.injectiveCochainCocycleClass_precompose
#print axioms LinearStudy.injectiveCochainCocycleClass_precompose
#check @LinearStudy.cochainCocycleOfHom_shifted
#print axioms LinearStudy.cochainCocycleOfHom_shifted
#check @LinearStudy.injectiveCochainClass_ofHom
#print axioms LinearStudy.injectiveCochainClass_ofHom
#check @LinearStudy.injectiveCochainClass_zero
#print axioms LinearStudy.injectiveCochainClass_zero
#check @LinearStudy.cochainSourceLiftClass_initial
#print axioms LinearStudy.cochainSourceLiftClass_initial
#check @LinearStudy.cochainSourceTerminalMap
#print axioms LinearStudy.cochainSourceTerminalMap
#check @LinearStudy.cochainSourceTerminalMap_isIso
#print axioms LinearStudy.cochainSourceTerminalMap_isIso
#check @LinearStudy.cochainSourceLiftClass_terminal
#print axioms LinearStudy.cochainSourceLiftClass_terminal
#print LinearStudy.cochainSourceTerminalMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.injectiveCochainCocycleClass_precompose,true),(`LinearStudy.cochainCocycleOfHom_shifted,true),(`LinearStudy.injectiveCochainClass_ofHom,true),(`LinearStudy.injectiveCochainClass_zero,true),(`LinearStudy.cochainSourceLiftClass_initial,true),(`LinearStudy.cochainSourceTerminalMap,false),(`LinearStudy.cochainSourceTerminalMap_isIso,true),(`LinearStudy.cochainSourceLiftClass_terminal,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
