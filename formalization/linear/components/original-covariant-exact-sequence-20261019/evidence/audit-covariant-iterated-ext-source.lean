module
import all Linear.IteratedCovariantExtClass
import all Linear.IteratedCovariantExtSurjective
import all Linear.IteratedCovariantExtInjective
import all Linear.IteratedCovariantExtExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.iteratedCovariantExtClass
#print axioms LinearStudy.iteratedCovariantExtClass
#check @LinearStudy.iteratedCovariantExtClass_zero
#print axioms LinearStudy.iteratedCovariantExtClass_zero
#check @LinearStudy.iteratedCovariantExtClass_succ
#print axioms LinearStudy.iteratedCovariantExtClass_succ
#check @LinearStudy.iteratedCovariantExtClass_postcomp_surjective
#print axioms LinearStudy.iteratedCovariantExtClass_postcomp_surjective
#check @LinearStudy.iteratedCovariantExtClass_postcomp_injective
#print axioms LinearStudy.iteratedCovariantExtClass_postcomp_injective
#check @LinearStudy.iteratedCovariantExtClass_kernel
#print axioms LinearStudy.iteratedCovariantExtClass_kernel
#print LinearStudy.iteratedCovariantExtClass
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.iteratedCovariantExtClass,false),(`LinearStudy.iteratedCovariantExtClass_zero,true),(`LinearStudy.iteratedCovariantExtClass_succ,true),(`LinearStudy.iteratedCovariantExtClass_postcomp_surjective,true),(`LinearStudy.iteratedCovariantExtClass_postcomp_injective,true),(`LinearStudy.iteratedCovariantExtClass_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
