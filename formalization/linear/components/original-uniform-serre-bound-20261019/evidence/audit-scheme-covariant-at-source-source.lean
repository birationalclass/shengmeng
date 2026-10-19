module
import all Linear.SchemeModuleOriginalCovariantAtSource
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalCovariantAtSourceStatement
#print axioms LinearStudy.schemeModuleOriginalCovariantAtSourceStatement
#check @LinearStudy.schemeModuleOriginalCovariantAtSourceStatement_proof
#print axioms LinearStudy.schemeModuleOriginalCovariantAtSourceStatement_proof
#print LinearStudy.schemeModuleOriginalCovariantAtSourceStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalCovariantAtSourceStatement,false),(`LinearStudy.schemeModuleOriginalCovariantAtSourceStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
