module
import all Linear.SchemeModuleOriginalCovariantExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalCovariant_surjective
#print axioms LinearStudy.schemeModuleOriginalCovariant_surjective
#check @LinearStudy.schemeModuleOriginalCovariant_kernel
#print axioms LinearStudy.schemeModuleOriginalCovariant_kernel
#check @LinearStudy.schemeModuleOriginalCovariantExactStatement
#print axioms LinearStudy.schemeModuleOriginalCovariantExactStatement
#check @LinearStudy.schemeModuleOriginalCovariantExactStatement_proof
#print axioms LinearStudy.schemeModuleOriginalCovariantExactStatement_proof
#print LinearStudy.schemeModuleOriginalCovariantExactStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalCovariant_surjective,true),(`LinearStudy.schemeModuleOriginalCovariant_kernel,true),(`LinearStudy.schemeModuleOriginalCovariantExactStatement,false),(`LinearStudy.schemeModuleOriginalCovariantExactStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
