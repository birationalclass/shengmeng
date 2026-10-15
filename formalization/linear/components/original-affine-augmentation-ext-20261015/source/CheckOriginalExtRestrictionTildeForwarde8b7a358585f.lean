module
import all Linear.TildeNativeModuleExtMappedChain
import all Linear.TildeKoszulExactTopExtMappedChain
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeNativeModuleExtMappedChainLaw
#print axioms LinearStudy.tildeNativeModuleExtMappedChainLaw
#check @LinearStudy.tildeNativeModuleExtMappedChainLaw_proof
#print axioms LinearStudy.tildeNativeModuleExtMappedChainLaw_proof
#check @LinearStudy.tildeKoszulExactTopExtMappedChain
#print axioms LinearStudy.tildeKoszulExactTopExtMappedChain
#print LinearStudy.tildeNativeModuleExtMappedChainLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeNativeModuleExtMappedChainLaw,false),(`LinearStudy.tildeNativeModuleExtMappedChainLaw_proof,true),(`LinearStudy.tildeKoszulExactTopExtMappedChain,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
