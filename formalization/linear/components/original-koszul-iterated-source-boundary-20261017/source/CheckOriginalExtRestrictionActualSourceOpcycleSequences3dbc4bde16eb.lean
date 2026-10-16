module
import all Linear.CochainOpcycleSourceSequence
import all Linear.CochainAugmentationOpcycle
import all Linear.ShortExactInjectiveBoundaryComponents
import all Linear.CochainOpcycleInjectiveBoundaryComponents
import all Linear.CochainOpcycleIteratedBoundary
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainOpcycleSourceSequence
#print axioms LinearStudy.cochainOpcycleSourceSequence
#check @LinearStudy.cochainOpcycleSourceSequenceIsCokernel
#print axioms LinearStudy.cochainOpcycleSourceSequenceIsCokernel
#check @LinearStudy.cochainOpcycleSourceSequence_shortExact
#print axioms LinearStudy.cochainOpcycleSourceSequence_shortExact
#check @LinearStudy.cochainAugmentation_exactAt_negative
#print axioms LinearStudy.cochainAugmentation_exactAt_negative
#check @LinearStudy.cochainAugmentationOpcycle
#print axioms LinearStudy.cochainAugmentationOpcycle
#check @LinearStudy.cochainAugmentationOpcycle_projection
#print axioms LinearStudy.cochainAugmentationOpcycle_projection
#check @LinearStudy.cochainAugmentationOpcycle_isIso
#print axioms LinearStudy.cochainAugmentationOpcycle_isIso
#check @LinearStudy.shortExactInjectiveExtBoundary_components
#print axioms LinearStudy.shortExactInjectiveExtBoundary_components
#check @LinearStudy.cochainOpcycleInjectiveBoundary_components
#print axioms LinearStudy.cochainOpcycleInjectiveBoundary_components
#check @LinearStudy.cochainSourceDegree
#print axioms LinearStudy.cochainSourceDegree
#check @LinearStudy.cochainSourceDegree_eq
#print axioms LinearStudy.cochainSourceDegree_eq
#check @LinearStudy.cochainOpcycleIteratedBoundary
#print axioms LinearStudy.cochainOpcycleIteratedBoundary
#check @LinearStudy.cochainOpcycleIteratedBoundary_succ
#print axioms LinearStudy.cochainOpcycleIteratedBoundary_succ
#print LinearStudy.cochainOpcycleSourceSequence
#print LinearStudy.cochainOpcycleSourceSequenceIsCokernel
#print LinearStudy.cochainAugmentationOpcycle
#print LinearStudy.cochainSourceDegree
#print LinearStudy.cochainOpcycleIteratedBoundary
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainOpcycleSourceSequence,false),(`LinearStudy.cochainOpcycleSourceSequenceIsCokernel,false),(`LinearStudy.cochainOpcycleSourceSequence_shortExact,true),(`LinearStudy.cochainAugmentation_exactAt_negative,true),(`LinearStudy.cochainAugmentationOpcycle,false),(`LinearStudy.cochainAugmentationOpcycle_projection,true),(`LinearStudy.cochainAugmentationOpcycle_isIso,true),(`LinearStudy.shortExactInjectiveExtBoundary_components,true),(`LinearStudy.cochainOpcycleInjectiveBoundary_components,true),(`LinearStudy.cochainSourceDegree,false),(`LinearStudy.cochainSourceDegree_eq,true),(`LinearStudy.cochainOpcycleIteratedBoundary,false),(`LinearStudy.cochainOpcycleIteratedBoundary_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
