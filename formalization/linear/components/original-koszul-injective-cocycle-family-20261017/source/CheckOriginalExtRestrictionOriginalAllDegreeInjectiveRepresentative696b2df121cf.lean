module
import all Linear.CochainKInjectiveDerivedCocycle
import all Linear.CochainResolutionInjectiveCocycle
import all Linear.CochainClassEqBoundary
import all Linear.OriginalChainOrderedTopCocycle
import all Linear.OriginalChainTopInjectiveCocycle
import all Linear.OriginalChainCokernelTopInjectiveCocycle
import all Linear.OriginalChainStandardTopInjectiveCocycle
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainKInjectiveDerivedCocycle_exists
#print axioms LinearStudy.cochainKInjectiveDerivedCocycle_exists
#check @LinearStudy.cochainKInjectiveClassEq_iff_derivedMapEq
#print axioms LinearStudy.cochainKInjectiveClassEq_iff_derivedMapEq
#check @LinearStudy.cochainResolutionInjectiveCocycle_exists
#print axioms LinearStudy.cochainResolutionInjectiveCocycle_exists
#check @LinearStudy.cochainClassEq_boundary_exists
#print axioms LinearStudy.cochainClassEq_boundary_exists
#check @LinearStudy.originalChainOrderedTopCocycle
#print axioms LinearStudy.originalChainOrderedTopCocycle
#check @LinearStudy.originalChainTopExtClass_orderedCocycle
#print axioms LinearStudy.originalChainTopExtClass_orderedCocycle
#check @LinearStudy.originalChainTopInjectiveCocycle_exists
#print axioms LinearStudy.originalChainTopInjectiveCocycle_exists
#check @LinearStudy.originalChainCokernelTopInjectiveCocycle_exists
#print axioms LinearStudy.originalChainCokernelTopInjectiveCocycle_exists
#check @LinearStudy.originalChainExplicitStandardTopInjectiveCocycleProof
#print axioms LinearStudy.originalChainExplicitStandardTopInjectiveCocycleProof
#print LinearStudy.originalChainOrderedTopCocycle
#print LinearStudy.originalChainExplicitStandardTopInjectiveCocycleProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainKInjectiveDerivedCocycle_exists,true),(`LinearStudy.cochainKInjectiveClassEq_iff_derivedMapEq,true),(`LinearStudy.cochainResolutionInjectiveCocycle_exists,true),(`LinearStudy.cochainClassEq_boundary_exists,true),(`LinearStudy.originalChainOrderedTopCocycle,false),(`LinearStudy.originalChainTopExtClass_orderedCocycle,true),(`LinearStudy.originalChainTopInjectiveCocycle_exists,true),(`LinearStudy.originalChainCokernelTopInjectiveCocycle_exists,true),(`LinearStudy.originalChainExplicitStandardTopInjectiveCocycleProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
