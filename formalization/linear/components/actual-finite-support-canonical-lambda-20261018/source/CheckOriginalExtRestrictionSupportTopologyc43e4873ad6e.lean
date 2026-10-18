module
import all Linear.ClosedDiscreteSupportSheafFlasque
import all Linear.DiscreteClosedMapSupportFlasque
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.closedDiscreteSupportAbelianSheaf_restriction_surjective
#print axioms LinearStudy.closedDiscreteSupportAbelianSheaf_restriction_surjective
#check @LinearStudy.closedDiscreteSupportAbelianSheaf_isFlasque
#print axioms LinearStudy.closedDiscreteSupportAbelianSheaf_isFlasque
#check @LinearStudy.discreteClosedMap_range_inter_open_isClosed
#print axioms LinearStudy.discreteClosedMap_range_inter_open_isClosed
#check @LinearStudy.discreteClosedMap_supportedAbelianSheaf_isFlasque
#print axioms LinearStudy.discreteClosedMap_supportedAbelianSheaf_isFlasque
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.closedDiscreteSupportAbelianSheaf_restriction_surjective,true),(`LinearStudy.closedDiscreteSupportAbelianSheaf_isFlasque,true),(`LinearStudy.discreteClosedMap_range_inter_open_isClosed,true),(`LinearStudy.discreteClosedMap_supportedAbelianSheaf_isFlasque,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
