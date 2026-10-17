module
import all Linear.OriginalChainTerminalSourceIso
import all Linear.SchemeModuleGlobalToInternalExtSourceIso
import all Linear.SchemeModuleOriginalSmallClassInternalImage
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainTerminalSourceIso
#print axioms LinearStudy.originalChainTerminalSourceIso
#check @LinearStudy.originalChainTerminalSourceIso_hom
#print axioms LinearStudy.originalChainTerminalSourceIso_hom
#check @LinearStudy.schemeModuleGlobalToInternalExtAll_sourceIso
#print axioms LinearStudy.schemeModuleGlobalToInternalExtAll_sourceIso
#check @LinearStudy.schemeModuleOriginalSmallClass_internalImage
#print axioms LinearStudy.schemeModuleOriginalSmallClass_internalImage
#print LinearStudy.originalChainTerminalSourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainTerminalSourceIso,false),(`LinearStudy.originalChainTerminalSourceIso_hom,true),(`LinearStudy.schemeModuleGlobalToInternalExtAll_sourceIso,true),(`LinearStudy.schemeModuleOriginalSmallClass_internalImage,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
