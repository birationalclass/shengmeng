module
import all Linear.OriginalChainDegreeOneConeMap
import all Linear.OriginalChainDegreeOneConeAugmentation
import all Linear.OriginalChainDegreeOneConeQuasiIso
import all Linear.OriginalChainDegreeOneConeTopCocycle
import all Linear.CochainResolutionSourceQuasiIso
import all Linear.CochainResolutionExtClassAdditive
import all Linear.CochainResolutionExtClassCongruence
import all Linear.OriginalChainDegreeOneRoofClass
import all Linear.OriginalChainDegreeOneBoundaryClass
import all Linear.OriginalChainDegreeOneInjectiveCocycle
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainDegreeOneConeMap
#print axioms LinearStudy.originalChainDegreeOneConeMap
#check @LinearStudy.originalChainFirstCokernelSequence
#print axioms LinearStudy.originalChainFirstCokernelSequence
#check @LinearStudy.originalChainDegreeOneConeMap_augmentation
#print axioms LinearStudy.originalChainDegreeOneConeMap_augmentation
#check @LinearStudy.originalChainFirstCokernelSequence_shortExact
#print axioms LinearStudy.originalChainFirstCokernelSequence_shortExact
#check @LinearStudy.originalChainDegreeOneConeMap_quasiIso
#print axioms LinearStudy.originalChainDegreeOneConeMap_quasiIso
#check @LinearStudy.originalChainDegreeOneConeMap_topCocycle
#print axioms LinearStudy.originalChainDegreeOneConeMap_topCocycle
#check @LinearStudy.originalChainDegreeOneConeMap_triangleTop
#print axioms LinearStudy.originalChainDegreeOneConeMap_triangleTop
#check @LinearStudy.cochainResolutionExtClass_sourceQuasiIso
#print axioms LinearStudy.cochainResolutionExtClass_sourceQuasiIso
#check @LinearStudy.cochainResolutionExtClass_neg
#print axioms LinearStudy.cochainResolutionExtClass_neg
#check @LinearStudy.cochainResolutionExtClass_congr
#print axioms LinearStudy.cochainResolutionExtClass_congr
#check @LinearStudy.originalChainDegreeOneTopExtClass_eq_neg_roof
#print axioms LinearStudy.originalChainDegreeOneTopExtClass_eq_neg_roof
#check @LinearStudy.originalChainDegreeOneTopExtClass_eq_boundary
#print axioms LinearStudy.originalChainDegreeOneTopExtClass_eq_boundary
#check @LinearStudy.originalChainDegreeOneInjectiveCocycleRealization
#print axioms LinearStudy.originalChainDegreeOneInjectiveCocycleRealization
#print LinearStudy.originalChainDegreeOneConeMap
#print LinearStudy.originalChainFirstCokernelSequence
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainDegreeOneConeMap,false),(`LinearStudy.originalChainFirstCokernelSequence,false),(`LinearStudy.originalChainDegreeOneConeMap_augmentation,true),(`LinearStudy.originalChainFirstCokernelSequence_shortExact,true),(`LinearStudy.originalChainDegreeOneConeMap_quasiIso,true),(`LinearStudy.originalChainDegreeOneConeMap_topCocycle,true),(`LinearStudy.originalChainDegreeOneConeMap_triangleTop,true),(`LinearStudy.cochainResolutionExtClass_sourceQuasiIso,true),(`LinearStudy.cochainResolutionExtClass_neg,true),(`LinearStudy.cochainResolutionExtClass_congr,true),(`LinearStudy.originalChainDegreeOneTopExtClass_eq_neg_roof,true),(`LinearStudy.originalChainDegreeOneTopExtClass_eq_boundary,true),(`LinearStudy.originalChainDegreeOneInjectiveCocycleRealization,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
