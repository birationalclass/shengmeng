module
import all Linear.SchemeModuleLocalInternalExtIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleLocalHomCoefficientComplexIso
#print axioms LinearStudy.schemeModuleLocalHomCoefficientComplexIso
#check @LinearStudy.schemeModuleLocalInternalExtSourceIso
#print axioms LinearStudy.schemeModuleLocalInternalExtSourceIso
#print LinearStudy.schemeModuleLocalHomCoefficientComplexIso
#print LinearStudy.schemeModuleLocalInternalExtSourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleLocalHomCoefficientComplexIso,false),(`LinearStudy.schemeModuleLocalInternalExtSourceIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
