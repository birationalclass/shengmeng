module
import all Linear.SchemeModuleInjectiveInternalHomBoundaryClass
import all Linear.ShortExactInjectiveNativeBoundaryComponents
import all Linear.ShortExactInjectiveNativeLifts
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary
#check @LinearStudy.shortExactInjectiveExtBoundary_nativeComponents
#print axioms LinearStudy.shortExactInjectiveExtBoundary_nativeComponents
#check @LinearStudy.shortExactInjectiveNativeLifts_exists
#print axioms LinearStudy.shortExactInjectiveNativeLifts_exists
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_boundary,true),(`LinearStudy.shortExactInjectiveExtBoundary_nativeComponents,true),(`LinearStudy.shortExactInjectiveNativeLifts_exists,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
