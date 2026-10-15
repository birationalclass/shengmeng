module
import all Linear.SchemeModuleInternalExtSourceExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceShortComplex
#print axioms LinearStudy.schemeModuleInternalExtSourceShortComplex
#check @LinearStudy.schemeModuleInternalExtSourceResolutionIso
#print axioms LinearStudy.schemeModuleInternalExtSourceResolutionIso
#check @LinearStudy.schemeModuleInternalExtSourceShortComplex_exact
#print axioms LinearStudy.schemeModuleInternalExtSourceShortComplex_exact
#print LinearStudy.schemeModuleInternalExtSourceShortComplex
#print LinearStudy.schemeModuleInternalExtSourceResolutionIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceShortComplex,false),(`LinearStudy.schemeModuleInternalExtSourceResolutionIso,false),(`LinearStudy.schemeModuleInternalExtSourceShortComplex_exact,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
