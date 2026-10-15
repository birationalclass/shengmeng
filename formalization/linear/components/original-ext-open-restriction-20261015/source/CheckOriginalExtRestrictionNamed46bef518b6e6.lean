module
import all Linear.SchemeModuleOriginalExtRestrictionLaw
import all Linear.OriginalProjectiveZeroChart
import all Linear.ProjectivePulledOriginalExtRestrictionLaw
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw
#print axioms LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw
#check @LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw_proof
#print axioms LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw_proof
#check @LinearStudy.originalProjectiveZeroChart
#print axioms LinearStudy.originalProjectiveZeroChart
#check @LinearStudy.originalProjectiveZeroChart_isOpenImmersion
#print axioms LinearStudy.originalProjectiveZeroChart_isOpenImmersion
#check @LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw
#print axioms LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw
#check @LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw_proof
#print axioms LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw_proof
#print LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw
#print LinearStudy.originalProjectiveZeroChart
#print LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw,false),(`LinearStudy.schemeModuleOriginalChainTopExtOpenRestrictionLaw_proof,true),(`LinearStudy.originalProjectiveZeroChart,false),(`LinearStudy.originalProjectiveZeroChart_isOpenImmersion,true),(`LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw,false),(`LinearStudy.projectivePulledOriginalWholeCutExtRestrictionLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
