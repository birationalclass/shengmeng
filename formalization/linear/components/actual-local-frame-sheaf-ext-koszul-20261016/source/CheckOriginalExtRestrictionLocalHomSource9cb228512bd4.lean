module
import all Linear.SchemeModuleLocalHomPrecompose
import all Linear.SchemeModuleLocalHomSourceIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleLocalHomPrecompose
#print axioms LinearStudy.schemeModuleLocalHomPrecompose
#check @LinearStudy.schemeModuleLocalHomPrecompose_id
#print axioms LinearStudy.schemeModuleLocalHomPrecompose_id
#check @LinearStudy.schemeModuleLocalHomPrecompose_comp
#print axioms LinearStudy.schemeModuleLocalHomPrecompose_comp
#check @LinearStudy.schemeModuleLocalHomSourceIso
#print axioms LinearStudy.schemeModuleLocalHomSourceIso
#check @LinearStudy.schemeModuleLocalHomCoefficientIso
#print axioms LinearStudy.schemeModuleLocalHomCoefficientIso
#print LinearStudy.schemeModuleLocalHomPrecompose
#print LinearStudy.schemeModuleLocalHomSourceIso
#print LinearStudy.schemeModuleLocalHomCoefficientIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleLocalHomPrecompose,false),(`LinearStudy.schemeModuleLocalHomPrecompose_id,true),(`LinearStudy.schemeModuleLocalHomPrecompose_comp,true),(`LinearStudy.schemeModuleLocalHomSourceIso,false),(`LinearStudy.schemeModuleLocalHomCoefficientIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
