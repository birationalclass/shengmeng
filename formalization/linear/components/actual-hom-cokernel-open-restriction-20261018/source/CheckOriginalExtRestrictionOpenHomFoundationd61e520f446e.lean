module
import all Linear.SchemeModuleHomOpenImmersionRestriction
import all Linear.SchemeModuleHomOpenImmersionBijective
import all Linear.SchemeModuleHomOpenImmersionMorphism
import all Linear.SchemeModuleHomOpenImmersionIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.openImmersionOverPost_isEquivalence
#print axioms LinearStudy.openImmersionOverPost_isEquivalence
#check @LinearStudy.schemeModuleHomOpenImmersionRestrictSection
#print axioms LinearStudy.schemeModuleHomOpenImmersionRestrictSection
#check @LinearStudy.schemeModuleHomOpenImmersionRestrictSection_evaluation
#print axioms LinearStudy.schemeModuleHomOpenImmersionRestrictSection_evaluation
#check @LinearStudy.schemeModuleHomOpenImmersionRestrictSection_bijective
#print axioms LinearStudy.schemeModuleHomOpenImmersionRestrictSection_bijective
#check @LinearStudy.schemeModuleHomOpenImmersionMorphism
#print axioms LinearStudy.schemeModuleHomOpenImmersionMorphism
#check @LinearStudy.schemeModuleHomOpenImmersionIso
#print axioms LinearStudy.schemeModuleHomOpenImmersionIso
#print LinearStudy.schemeModuleHomOpenImmersionRestrictSection
#print LinearStudy.schemeModuleHomOpenImmersionMorphism
#print LinearStudy.schemeModuleHomOpenImmersionIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.openImmersionOverPost_isEquivalence,true),(`LinearStudy.schemeModuleHomOpenImmersionRestrictSection,false),(`LinearStudy.schemeModuleHomOpenImmersionRestrictSection_evaluation,true),(`LinearStudy.schemeModuleHomOpenImmersionRestrictSection_bijective,true),(`LinearStudy.schemeModuleHomOpenImmersionMorphism,false),(`LinearStudy.schemeModuleHomOpenImmersionIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
