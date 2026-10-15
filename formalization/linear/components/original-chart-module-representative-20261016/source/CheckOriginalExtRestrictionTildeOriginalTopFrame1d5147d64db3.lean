module
import all Linear.TildeKoszulOriginalTopModuleFrame
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeKoszulOriginalTopCoefficientIso
#print axioms LinearStudy.tildeKoszulOriginalTopCoefficientIso
#check @LinearStudy.tildeKoszulOriginalTopFunctional_preimage_id
#print axioms LinearStudy.tildeKoszulOriginalTopFunctional_preimage_id
#check @LinearStudy.tildeKoszulOriginalTopModuleExt_eq_identity
#print axioms LinearStudy.tildeKoszulOriginalTopModuleExt_eq_identity
#check @LinearStudy.tildeKoszulOriginalTopModuleFrameLaw
#print axioms LinearStudy.tildeKoszulOriginalTopModuleFrameLaw
#check @LinearStudy.tildeKoszulOriginalTopModuleFrameLaw_proof
#print axioms LinearStudy.tildeKoszulOriginalTopModuleFrameLaw_proof
#print LinearStudy.tildeKoszulOriginalTopCoefficientIso
#print LinearStudy.tildeKoszulOriginalTopModuleFrameLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeKoszulOriginalTopCoefficientIso,false),(`LinearStudy.tildeKoszulOriginalTopFunctional_preimage_id,true),(`LinearStudy.tildeKoszulOriginalTopModuleExt_eq_identity,true),(`LinearStudy.tildeKoszulOriginalTopModuleFrameLaw,false),(`LinearStudy.tildeKoszulOriginalTopModuleFrameLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
