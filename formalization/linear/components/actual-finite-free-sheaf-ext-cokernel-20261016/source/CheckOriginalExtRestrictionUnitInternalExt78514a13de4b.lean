module
import all Linear.SchemeModuleUnitInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteLimits
#print axioms LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteLimits
#check @LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteColimits
#print axioms LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteColimits
#check @LinearStudy.schemeModuleUnitInternalExtResolutionIso
#print axioms LinearStudy.schemeModuleUnitInternalExtResolutionIso
#check @LinearStudy.schemeModuleUnitInternalExt_succ
#print axioms LinearStudy.schemeModuleUnitInternalExt_succ
#print LinearStudy.schemeModuleUnitInternalExtResolutionIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteLimits,true),(`LinearStudy.schemeModuleUnitHomCoefficient_preservesFiniteColimits,true),(`LinearStudy.schemeModuleUnitInternalExtResolutionIso,false),(`LinearStudy.schemeModuleUnitInternalExt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
