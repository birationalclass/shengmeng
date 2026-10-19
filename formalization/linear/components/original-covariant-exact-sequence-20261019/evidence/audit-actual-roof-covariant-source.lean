module
import all Linear.CochainActualRoofCovariantExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochain_pOpcycles_index_transport
#print axioms LinearStudy.cochain_pOpcycles_index_transport
#check @LinearStudy.cochainActualRoofCovariant_surjective
#print axioms LinearStudy.cochainActualRoofCovariant_surjective
#check @LinearStudy.cochainActualRoofCovariant_kernel
#print axioms LinearStudy.cochainActualRoofCovariant_kernel
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochain_pOpcycles_index_transport,true),(`LinearStudy.cochainActualRoofCovariant_surjective,true),(`LinearStudy.cochainActualRoofCovariant_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
