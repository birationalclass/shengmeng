module
import all Linear.MappedChainPresentationExtComparison
import all Linear.ChainCokernelAugmentationSourceEq
import all Linear.MappedChainPresentationOriginalExt
import all Linear.MappedChainPresentationNamedExt
import all Linear.StandardMappedChainPresentationNamedExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.mappedChainPresentationAugmentationTargetIso
#print axioms LinearStudy.mappedChainPresentationAugmentationTargetIso
#check @LinearStudy.mappedChainPresentationCoforkAugmentation_quasiIso
#print axioms LinearStudy.mappedChainPresentationCoforkAugmentation_quasiIso
#check @LinearStudy.mappedChainPresentationTopExtClass_comparison
#print axioms LinearStudy.mappedChainPresentationTopExtClass_comparison
#check @LinearStudy.originalChainCokernelTargetAugmentation_sourceEq
#print axioms LinearStudy.originalChainCokernelTargetAugmentation_sourceEq
#check @LinearStudy.originalChainCokernelTargetAugmentation_quasiIso_sourceEq
#print axioms LinearStudy.originalChainCokernelTargetAugmentation_quasiIso_sourceEq
#check @LinearStudy.originalChainTopExtClass_cokernelSourceEq
#print axioms LinearStudy.originalChainTopExtClass_cokernelSourceEq
#check @LinearStudy.mappedChainPresentationOriginalTopFunctional
#print axioms LinearStudy.mappedChainPresentationOriginalTopFunctional
#check @LinearStudy.mappedChainPresentationOriginalTopFunctional_isCocycle
#print axioms LinearStudy.mappedChainPresentationOriginalTopFunctional_isCocycle
#check @LinearStudy.mappedChainPresentationOriginalTopExt_comparison
#print axioms LinearStudy.mappedChainPresentationOriginalTopExt_comparison
#check @LinearStudy.mappedChainPresentationOriginalExt_mapExactFunctor
#print axioms LinearStudy.mappedChainPresentationOriginalExt_mapExactFunctor
#check @LinearStudy.mappedChainPresentationNamedExtLaw
#print axioms LinearStudy.mappedChainPresentationNamedExtLaw
#check @LinearStudy.mappedChainPresentationNamedExtLaw_proof
#print axioms LinearStudy.mappedChainPresentationNamedExtLaw_proof
#check @LinearStudy.standardMappedChainPresentationNamedExtLaw
#print axioms LinearStudy.standardMappedChainPresentationNamedExtLaw
#check @LinearStudy.standardMappedChainPresentationNamedExtLaw_proof
#print axioms LinearStudy.standardMappedChainPresentationNamedExtLaw_proof
#print LinearStudy.mappedChainPresentationAugmentationTargetIso
#print LinearStudy.mappedChainPresentationOriginalTopFunctional
#print LinearStudy.mappedChainPresentationNamedExtLaw
#print LinearStudy.standardMappedChainPresentationNamedExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.mappedChainPresentationAugmentationTargetIso,false),(`LinearStudy.mappedChainPresentationCoforkAugmentation_quasiIso,true),(`LinearStudy.mappedChainPresentationTopExtClass_comparison,true),(`LinearStudy.originalChainCokernelTargetAugmentation_sourceEq,true),(`LinearStudy.originalChainCokernelTargetAugmentation_quasiIso_sourceEq,true),(`LinearStudy.originalChainTopExtClass_cokernelSourceEq,true),(`LinearStudy.mappedChainPresentationOriginalTopFunctional,false),(`LinearStudy.mappedChainPresentationOriginalTopFunctional_isCocycle,true),(`LinearStudy.mappedChainPresentationOriginalTopExt_comparison,true),(`LinearStudy.mappedChainPresentationOriginalExt_mapExactFunctor,true),(`LinearStudy.mappedChainPresentationNamedExtLaw,false),(`LinearStudy.mappedChainPresentationNamedExtLaw_proof,true),(`LinearStudy.standardMappedChainPresentationNamedExtLaw,false),(`LinearStudy.standardMappedChainPresentationNamedExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
