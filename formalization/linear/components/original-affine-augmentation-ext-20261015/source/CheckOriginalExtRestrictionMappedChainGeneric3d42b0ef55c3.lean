module
import all Linear.ChainTopExtExactFunctorMappedChain
import all Linear.ChainStandardMappedExtLaw
import all Linear.SchemeModuleOriginalMappedChainExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainTopExtClass_mapExactFunctor_eq_mappedChain
#print axioms LinearStudy.originalChainTopExtClass_mapExactFunctor_eq_mappedChain
#check @LinearStudy.originalChainStandardMappedExtLaw
#print axioms LinearStudy.originalChainStandardMappedExtLaw
#check @LinearStudy.originalChainStandardMappedExtLaw_proof
#print axioms LinearStudy.originalChainStandardMappedExtLaw_proof
#check @LinearStudy.schemeModuleOriginalMappedChainExtLaw
#print axioms LinearStudy.schemeModuleOriginalMappedChainExtLaw
#check @LinearStudy.schemeModuleOriginalMappedChainExtLaw_proof
#print axioms LinearStudy.schemeModuleOriginalMappedChainExtLaw_proof
#print LinearStudy.originalChainStandardMappedExtLaw
#print LinearStudy.schemeModuleOriginalMappedChainExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainTopExtClass_mapExactFunctor_eq_mappedChain,true),(`LinearStudy.originalChainStandardMappedExtLaw,false),(`LinearStudy.originalChainStandardMappedExtLaw_proof,true),(`LinearStudy.schemeModuleOriginalMappedChainExtLaw,false),(`LinearStudy.schemeModuleOriginalMappedChainExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
