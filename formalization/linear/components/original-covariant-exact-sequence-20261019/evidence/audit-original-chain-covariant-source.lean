module
import all Linear.OriginalChainCovariantExact
import all Linear.OriginalChainCovariantCoefficientIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainCovariant_middle_acyclic
#print axioms LinearStudy.originalChainCovariant_middle_acyclic
#check @LinearStudy.originalChainCovariant_surjective
#print axioms LinearStudy.originalChainCovariant_surjective
#check @LinearStudy.originalChainCovariant_kernel
#print axioms LinearStudy.originalChainCovariant_kernel
#check @LinearStudy.originalChainCovariantCoefficientIso_surjective
#print axioms LinearStudy.originalChainCovariantCoefficientIso_surjective
#check @LinearStudy.originalChainCovariantCoefficientIso_kernel
#print axioms LinearStudy.originalChainCovariantCoefficientIso_kernel
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainCovariant_middle_acyclic,true),(`LinearStudy.originalChainCovariant_surjective,true),(`LinearStudy.originalChainCovariant_kernel,true),(`LinearStudy.originalChainCovariantCoefficientIso_surjective,true),(`LinearStudy.originalChainCovariantCoefficientIso_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
