module
import all Linear.AdditiveFunctorExtendNaturality
import all Linear.AdditiveFunctorExtendSingleCompatibility
import all Linear.OriginalChainMappedAugmentationComparison
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.additiveFunctorExtendXIso_naturality
#print axioms LinearStudy.additiveFunctorExtendXIso_naturality
#check @LinearStudy.additiveFunctorExtendComplexIso_naturality
#print axioms LinearStudy.additiveFunctorExtendComplexIso_naturality
#check @LinearStudy.additiveFunctorExtendXIso_comp_XIso
#print axioms LinearStudy.additiveFunctorExtendXIso_comp_XIso
#check @LinearStudy.additiveFunctorExtendSingleIso_compatibility
#print axioms LinearStudy.additiveFunctorExtendSingleIso_compatibility
#check @LinearStudy.additiveFunctorOriginalChainCochainIso
#print axioms LinearStudy.additiveFunctorOriginalChainCochainIso
#check @LinearStudy.mappedOriginalChainAugmentation
#print axioms LinearStudy.mappedOriginalChainAugmentation
#check @LinearStudy.mappedOriginalChainAugmentation_asCochain
#print axioms LinearStudy.mappedOriginalChainAugmentation_asCochain
#print LinearStudy.additiveFunctorOriginalChainCochainIso
#print LinearStudy.mappedOriginalChainAugmentation
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.additiveFunctorExtendXIso_naturality,true),(`LinearStudy.additiveFunctorExtendComplexIso_naturality,true),(`LinearStudy.additiveFunctorExtendXIso_comp_XIso,true),(`LinearStudy.additiveFunctorExtendSingleIso_compatibility,true),(`LinearStudy.additiveFunctorOriginalChainCochainIso,false),(`LinearStudy.mappedOriginalChainAugmentation,false),(`LinearStudy.mappedOriginalChainAugmentation_asCochain,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
