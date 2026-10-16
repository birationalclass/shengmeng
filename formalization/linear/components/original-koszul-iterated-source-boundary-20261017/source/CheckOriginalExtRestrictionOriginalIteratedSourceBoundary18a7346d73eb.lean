module
import all Linear.CochainResolutionSourceBoundaryFamily
import all Linear.CochainResolutionSourceBoundaryClass
import all Linear.CochainResolutionIteratedSourceBoundary
import all Linear.OriginalChainIteratedSourceBoundary
import all Linear.OriginalChainStandardSourceBoundaryStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainResolutionSourceBoundaryFamily_exists
#print axioms LinearStudy.cochainResolutionSourceBoundaryFamily_exists
#check @LinearStudy.cochainResolutionSourceBoundaryClass_exists
#print axioms LinearStudy.cochainResolutionSourceBoundaryClass_exists
#check @LinearStudy.cochainTopOpcycleFunctional
#print axioms LinearStudy.cochainTopOpcycleFunctional
#check @LinearStudy.cochainResolutionTopExtClass_iteratedSourceBoundary
#print axioms LinearStudy.cochainResolutionTopExtClass_iteratedSourceBoundary
#check @LinearStudy.originalChainTopFunctionalCochain_closed
#print axioms LinearStudy.originalChainTopFunctionalCochain_closed
#check @LinearStudy.originalChainTopOpcycleFunctional
#print axioms LinearStudy.originalChainTopOpcycleFunctional
#check @LinearStudy.originalChainTopExtClass_iteratedSourceBoundary
#print axioms LinearStudy.originalChainTopExtClass_iteratedSourceBoundary
#check @LinearStudy.originalChainStandardSourceBoundaryStatement
#print axioms LinearStudy.originalChainStandardSourceBoundaryStatement
#check @LinearStudy.originalChainStandardSourceBoundaryStatement_proof
#print axioms LinearStudy.originalChainStandardSourceBoundaryStatement_proof
#print LinearStudy.cochainTopOpcycleFunctional
#print LinearStudy.originalChainTopOpcycleFunctional
#print LinearStudy.originalChainStandardSourceBoundaryStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainResolutionSourceBoundaryFamily_exists,true),(`LinearStudy.cochainResolutionSourceBoundaryClass_exists,true),(`LinearStudy.cochainTopOpcycleFunctional,false),(`LinearStudy.cochainResolutionTopExtClass_iteratedSourceBoundary,true),(`LinearStudy.originalChainTopFunctionalCochain_closed,true),(`LinearStudy.originalChainTopOpcycleFunctional,false),(`LinearStudy.originalChainTopExtClass_iteratedSourceBoundary,true),(`LinearStudy.originalChainStandardSourceBoundaryStatement,false),(`LinearStudy.originalChainStandardSourceBoundaryStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
