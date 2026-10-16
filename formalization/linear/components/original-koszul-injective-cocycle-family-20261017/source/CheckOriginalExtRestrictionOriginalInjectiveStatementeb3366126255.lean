module
import all Linear.OriginalChainStandardTopInjectiveStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainExplicitStandardTopInjectiveStatement
#print axioms LinearStudy.originalChainExplicitStandardTopInjectiveStatement
#check @LinearStudy.originalChainExplicitStandardTopInjectiveStatement_proof
#print axioms LinearStudy.originalChainExplicitStandardTopInjectiveStatement_proof
#print LinearStudy.originalChainExplicitStandardTopInjectiveStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainExplicitStandardTopInjectiveStatement,false),(`LinearStudy.originalChainExplicitStandardTopInjectiveStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
