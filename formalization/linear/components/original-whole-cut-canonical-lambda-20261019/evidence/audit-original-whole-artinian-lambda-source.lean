module
import all Linear.ProjectivePulledWholeCutArtinian
import all Linear.ProjectivePulledWholeCutLambdaFamily
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledLinearSection_exists_wholeCut_isArtinian
#print axioms LinearStudy.projectivePulledLinearSection_exists_wholeCut_isArtinian
#check @LinearStudy.projectivePulledLinearSection_exists_wholeCutCanonicalLambda_bijective
#print axioms LinearStudy.projectivePulledLinearSection_exists_wholeCutCanonicalLambda_bijective
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledLinearSection_exists_wholeCut_isArtinian,true),(`LinearStudy.projectivePulledLinearSection_exists_wholeCutCanonicalLambda_bijective,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
