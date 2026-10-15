module
import all Linear.MappedChainCokernelAugmentationSquare
import all Linear.MappedChainCokernelAugmentationLaw
import all Linear.MappedChainPresentationAugmentation
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainCoforkAugmentation
#print axioms LinearStudy.originalChainCoforkAugmentation
#check @LinearStudy.mappedOriginalChainTargetCokernelChartIso
#print axioms LinearStudy.mappedOriginalChainTargetCokernelChartIso
#check @LinearStudy.mappedOriginalChainAugmentation_f_zero
#print axioms LinearStudy.mappedOriginalChainAugmentation_f_zero
#check @LinearStudy.mappedOriginalChainCokernelTargetAugmentation_chart_comm
#print axioms LinearStudy.mappedOriginalChainCokernelTargetAugmentation_chart_comm
#check @LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw
#print axioms LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw
#check @LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw_proof
#print axioms LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw_proof
#check @LinearStudy.mappedChainPresentationAugmentationLaw
#print axioms LinearStudy.mappedChainPresentationAugmentationLaw
#check @LinearStudy.mappedChainPresentationAugmentationLaw_proof
#print axioms LinearStudy.mappedChainPresentationAugmentationLaw_proof
#print LinearStudy.originalChainCoforkAugmentation
#print LinearStudy.mappedOriginalChainTargetCokernelChartIso
#print LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw
#print LinearStudy.mappedChainPresentationAugmentationLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainCoforkAugmentation,false),(`LinearStudy.mappedOriginalChainTargetCokernelChartIso,false),(`LinearStudy.mappedOriginalChainAugmentation_f_zero,true),(`LinearStudy.mappedOriginalChainCokernelTargetAugmentation_chart_comm,true),(`LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw,false),(`LinearStudy.mappedOriginalChainCokernelAugmentationChartLaw_proof,true),(`LinearStudy.mappedChainPresentationAugmentationLaw,false),(`LinearStudy.mappedChainPresentationAugmentationLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
