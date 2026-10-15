module
import all Linear.OverOpenInjectiveRestriction
import all Linear.SchemeModuleOpenInjectives
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.overOpenRestriction_isRightAdjoint
#print axioms LinearStudy.overOpenRestriction_isRightAdjoint
#check @LinearStudy.overOpenRestriction_preservesInjectiveObjects
#print axioms LinearStudy.overOpenRestriction_preservesInjectiveObjects
#check @LinearStudy.schemeModuleOverFunctor_isRightAdjoint
#print axioms LinearStudy.schemeModuleOverFunctor_isRightAdjoint
#check @LinearStudy.schemeModuleOverFunctor_preservesInjectiveObjects
#print axioms LinearStudy.schemeModuleOverFunctor_preservesInjectiveObjects
#check @LinearStudy.schemeModuleInjectiveOver
#print axioms LinearStudy.schemeModuleInjectiveOver
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.overOpenRestriction_isRightAdjoint,true),(`LinearStudy.overOpenRestriction_preservesInjectiveObjects,true),(`LinearStudy.schemeModuleOverFunctor_isRightAdjoint,true),(`LinearStudy.schemeModuleOverFunctor_preservesInjectiveObjects,true),(`LinearStudy.schemeModuleInjectiveOver,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
