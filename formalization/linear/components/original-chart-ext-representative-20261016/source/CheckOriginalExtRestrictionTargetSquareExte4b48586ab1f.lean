module
import all Linear.CochainResolutionTargetIso
import all Linear.OriginalChainTopExtTargetIso
import all Linear.OriginalChainAugmentationSquareExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainResolutionExtClass_targetIso
#print axioms LinearStudy.cochainResolutionExtClass_targetIso
#check @LinearStudy.originalChainAugmentationAsCochain_target_comp
#print axioms LinearStudy.originalChainAugmentationAsCochain_target_comp
#check @LinearStudy.originalChainTopExtClass_targetIso
#print axioms LinearStudy.originalChainTopExtClass_targetIso
#check @LinearStudy.originalChainAugmentationSquare_quasiIso
#print axioms LinearStudy.originalChainAugmentationSquare_quasiIso
#check @LinearStudy.originalChainTopExtClass_augmentationSquare
#print axioms LinearStudy.originalChainTopExtClass_augmentationSquare
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainResolutionExtClass_targetIso,true),(`LinearStudy.originalChainAugmentationAsCochain_target_comp,true),(`LinearStudy.originalChainTopExtClass_targetIso,true),(`LinearStudy.originalChainAugmentationSquare_quasiIso,true),(`LinearStudy.originalChainTopExtClass_augmentationSquare,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
