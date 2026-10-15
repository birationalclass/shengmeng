module
import all Linear.SchemeModuleCanonicalGlobalToInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleGlobalToInternalExt
#print axioms LinearStudy.schemeModuleGlobalToInternalExt
#check @LinearStudy.schemeModuleGlobalToInternalExt_eq_viaResolution
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_eq_viaResolution
#check @LinearStudy.schemeModuleGlobalToInternalExt_naturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_naturality
#check @LinearStudy.schemeModuleGlobalToInternalExtSections
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections
#print LinearStudy.schemeModuleGlobalToInternalExt
#print LinearStudy.schemeModuleGlobalToInternalExtSections
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleGlobalToInternalExt,false),(`LinearStudy.schemeModuleGlobalToInternalExt_eq_viaResolution,true),(`LinearStudy.schemeModuleGlobalToInternalExt_naturality,true),(`LinearStudy.schemeModuleGlobalToInternalExtSections,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
