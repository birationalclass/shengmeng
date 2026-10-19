module
import all Linear.CochainOpcycleSignedExtension
import all Linear.CochainOpcycleSignedExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainOpcycleSignedExtension
#print axioms LinearStudy.cochainOpcycleSignedExtension
#check @LinearStudy.cochainOpcycleSignedExtension_eq_unit_smul_unsigned
#print axioms LinearStudy.cochainOpcycleSignedExtension_eq_unit_smul_unsigned
#check @LinearStudy.cochainOpcycleSignedExtension_surjective
#print axioms LinearStudy.cochainOpcycleSignedExtension_surjective
#check @LinearStudy.cochainOpcycleSignedExtension_kernel
#print axioms LinearStudy.cochainOpcycleSignedExtension_kernel
#print LinearStudy.cochainOpcycleSignedExtension
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainOpcycleSignedExtension,false),(`LinearStudy.cochainOpcycleSignedExtension_eq_unit_smul_unsigned,true),(`LinearStudy.cochainOpcycleSignedExtension_surjective,true),(`LinearStudy.cochainOpcycleSignedExtension_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
