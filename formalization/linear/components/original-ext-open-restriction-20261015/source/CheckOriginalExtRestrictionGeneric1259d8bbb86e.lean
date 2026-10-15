module
import all Linear.CochainResolutionExactFunctorObjects
import all Linear.CochainResolutionExactFunctorCompatibility
import all Linear.ChainTopExtExactFunctorCompatibility
import all Linear.ChainStandardTopExtExactFunctorProof
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.mappedCochainResolutionAugmentation
#print axioms LinearStudy.mappedCochainResolutionAugmentation
#check @LinearStudy.mappedCochainResolutionAugmentation_quasiIso
#print axioms LinearStudy.mappedCochainResolutionAugmentation_quasiIso
#check @LinearStudy.mappedCochainResolutionCocycle
#print axioms LinearStudy.mappedCochainResolutionCocycle
#check @LinearStudy.mappedCochainResolutionExtClass
#print axioms LinearStudy.mappedCochainResolutionExtClass
#check @LinearStudy.cochainResolutionExtClass_mapExactFunctor
#print axioms LinearStudy.cochainResolutionExtClass_mapExactFunctor
#check @LinearStudy.originalChainTopShiftedCocycle
#print axioms LinearStudy.originalChainTopShiftedCocycle
#check @LinearStudy.originalChainTopExtClass_eq_cochain
#print axioms LinearStudy.originalChainTopExtClass_eq_cochain
#check @LinearStudy.originalChainMappedTopExtClass
#print axioms LinearStudy.originalChainMappedTopExtClass
#check @LinearStudy.originalChainTopExtClass_mapExactFunctor
#print axioms LinearStudy.originalChainTopExtClass_mapExactFunctor
#check @LinearStudy.originalChainExplicitStandardTopExtClassMapProof
#print axioms LinearStudy.originalChainExplicitStandardTopExtClassMapProof
#print LinearStudy.mappedCochainResolutionAugmentation
#print LinearStudy.mappedCochainResolutionCocycle
#print LinearStudy.mappedCochainResolutionExtClass
#print LinearStudy.originalChainTopShiftedCocycle
#print LinearStudy.originalChainMappedTopExtClass
#print LinearStudy.originalChainExplicitStandardTopExtClassMapProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.mappedCochainResolutionAugmentation,false),(`LinearStudy.mappedCochainResolutionAugmentation_quasiIso,true),(`LinearStudy.mappedCochainResolutionCocycle,false),(`LinearStudy.mappedCochainResolutionExtClass,false),(`LinearStudy.cochainResolutionExtClass_mapExactFunctor,true),(`LinearStudy.originalChainTopShiftedCocycle,false),(`LinearStudy.originalChainTopExtClass_eq_cochain,true),(`LinearStudy.originalChainMappedTopExtClass,false),(`LinearStudy.originalChainTopExtClass_mapExactFunctor,true),(`LinearStudy.originalChainExplicitStandardTopExtClassMapProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
