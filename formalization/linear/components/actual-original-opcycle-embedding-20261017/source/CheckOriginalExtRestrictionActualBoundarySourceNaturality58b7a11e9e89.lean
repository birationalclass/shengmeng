module
import all Linear.SchemeModuleHomShortComplexSourceMap
import all Linear.SchemeModuleInternalExtBoundarySourceNaturality
import all Linear.SchemeModuleOriginalBoundaryEmbedding
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomShortComplexSourceMap
#print axioms LinearStudy.schemeModuleHomShortComplexSourceMap
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_sourceNaturality
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_sourceNaturality
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_sourceNaturality
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_sourceNaturality
#check @LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding
#print axioms LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding
#print LinearStudy.schemeModuleHomShortComplexSourceMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomShortComplexSourceMap,false),(`LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_sourceNaturality,true),(`LinearStudy.schemeModuleInternalExtSourceBoundary_sourceNaturality,true),(`LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
