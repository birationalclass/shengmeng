module
import all Linear.CochainOpcycleUnsignedExtension
import all Linear.CochainOpcycleUnsignedExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainOpcycleUnsignedExtension
#print axioms LinearStudy.cochainOpcycleUnsignedExtension
#check @LinearStudy.cochainOpcycleUnsignedExtension_zero
#print axioms LinearStudy.cochainOpcycleUnsignedExtension_zero
#check @LinearStudy.cochainOpcycleUnsignedExtension_succ
#print axioms LinearStudy.cochainOpcycleUnsignedExtension_succ
#check @LinearStudy.cochainOpcycleUnsignedExtension_surjective
#print axioms LinearStudy.cochainOpcycleUnsignedExtension_surjective
#check @LinearStudy.cochainOpcycleUnsignedExtension_kernel
#print axioms LinearStudy.cochainOpcycleUnsignedExtension_kernel
#print LinearStudy.cochainOpcycleUnsignedExtension
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainOpcycleUnsignedExtension,false),(`LinearStudy.cochainOpcycleUnsignedExtension_zero,true),(`LinearStudy.cochainOpcycleUnsignedExtension_succ,true),(`LinearStudy.cochainOpcycleUnsignedExtension_surjective,true),(`LinearStudy.cochainOpcycleUnsignedExtension_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
