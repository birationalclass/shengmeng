module
public meta import Lean.Elab.Command
import all Linear.ParameterFamilyEnrichSharedFacts
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.parameterFamily_enrich_from_sharedFacts
#print axioms LinearStudy.parameterFamily_enrich_from_sharedFacts
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.parameterFamily_enrich_from_sharedFacts,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
