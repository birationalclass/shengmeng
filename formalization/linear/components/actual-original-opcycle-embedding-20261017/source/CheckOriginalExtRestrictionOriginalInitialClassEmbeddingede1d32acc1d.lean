module
import all Linear.SchemeModuleHomZeroSourceNaturality
import all Linear.OriginalChainTopOpcycleEmbedding
import all Linear.SchemeModuleOriginalTopInitialClassEmbedding
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomToInternalExtZero_sourceNaturality
#print axioms LinearStudy.schemeModuleHomToInternalExtZero_sourceNaturality
#check @LinearStudy.schemeModuleGlobalToInternalExtAll_sourceNaturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExtAll_sourceNaturality
#check @LinearStudy.originalChainTopOpcycleFunctional_embedding
#print axioms LinearStudy.originalChainTopOpcycleFunctional_embedding
#check @LinearStudy.schemeModuleOriginalTopInitialClass_embedding
#print axioms LinearStudy.schemeModuleOriginalTopInitialClass_embedding
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomToInternalExtZero_sourceNaturality,true),(`LinearStudy.schemeModuleGlobalToInternalExtAll_sourceNaturality,true),(`LinearStudy.originalChainTopOpcycleFunctional_embedding,true),(`LinearStudy.schemeModuleOriginalTopInitialClass_embedding,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
