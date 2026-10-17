module
import all Linear.SchemeModuleHomToInternalExtZero
import all Linear.SchemeModuleHomZeroInjectiveCycle
import all Linear.InjectiveNativeDegreeZeroClass
import all Linear.SchemeModuleHomZeroInjectiveClass
import all Linear.SchemeModuleGlobalToInternalExtZeroBoundary
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomToInternalExtZero
#print axioms LinearStudy.schemeModuleHomToInternalExtZero
#check @LinearStudy.schemeModuleHomZeroInjectiveCycle
#print axioms LinearStudy.schemeModuleHomZeroInjectiveCycle
#check @LinearStudy.injectiveNativeExtMk_ofHom
#print axioms LinearStudy.injectiveNativeExtMk_ofHom
#check @LinearStudy.schemeModuleHomToInternalExtZero_viaResolution
#print axioms LinearStudy.schemeModuleHomToInternalExtZero_viaResolution
#check @LinearStudy.schemeModuleHomToInternalExtZero_boundary
#print axioms LinearStudy.schemeModuleHomToInternalExtZero_boundary
#print LinearStudy.schemeModuleHomToInternalExtZero
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomToInternalExtZero,false),(`LinearStudy.schemeModuleHomZeroInjectiveCycle,true),(`LinearStudy.injectiveNativeExtMk_ofHom,true),(`LinearStudy.schemeModuleHomToInternalExtZero_viaResolution,true),(`LinearStudy.schemeModuleHomToInternalExtZero_boundary,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
