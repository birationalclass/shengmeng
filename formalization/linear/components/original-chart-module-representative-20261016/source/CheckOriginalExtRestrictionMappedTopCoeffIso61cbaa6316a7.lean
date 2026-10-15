module
import all Linear.MappedChainPresentationTopCoefficientIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.mappedChainPresentationTermIso
#print axioms LinearStudy.mappedChainPresentationTermIso
#check @LinearStudy.mappedChainPresentationOriginalTopIso
#print axioms LinearStudy.mappedChainPresentationOriginalTopIso
#check @LinearStudy.mappedChainPresentationOriginalTopIso_hom
#print axioms LinearStudy.mappedChainPresentationOriginalTopIso_hom
#check @LinearStudy.mappedChainPresentationOriginalTopIso_normalize
#print axioms LinearStudy.mappedChainPresentationOriginalTopIso_normalize
#print LinearStudy.mappedChainPresentationTermIso
#print LinearStudy.mappedChainPresentationOriginalTopIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.mappedChainPresentationTermIso,false),(`LinearStudy.mappedChainPresentationOriginalTopIso,false),(`LinearStudy.mappedChainPresentationOriginalTopIso_hom,true),(`LinearStudy.mappedChainPresentationOriginalTopIso_normalize,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
