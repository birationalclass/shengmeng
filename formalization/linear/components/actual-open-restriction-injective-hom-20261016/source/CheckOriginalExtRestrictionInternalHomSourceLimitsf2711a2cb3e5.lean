module
import all Linear.SchemeModuleInternalHomSourceLimits
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalHomSourceSectionIso
#print axioms LinearStudy.schemeModuleInternalHomSourceSectionIso
#check @LinearStudy.schemeModuleOverFunctor_preservesFiniteColimits
#print axioms LinearStudy.schemeModuleOverFunctor_preservesFiniteColimits
#check @LinearStudy.schemeModuleInternalHomFunctor_preservesFiniteLimits
#print axioms LinearStudy.schemeModuleInternalHomFunctor_preservesFiniteLimits
#print LinearStudy.schemeModuleInternalHomSourceSectionIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalHomSourceSectionIso,false),(`LinearStudy.schemeModuleOverFunctor_preservesFiniteColimits,true),(`LinearStudy.schemeModuleInternalHomFunctor_preservesFiniteLimits,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
