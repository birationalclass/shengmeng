module
import all Linear.CochainActualTopCovariantExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainActualTopOpcycleIso
#print axioms LinearStudy.cochainActualTopOpcycleIso
#check @LinearStudy.cochainActualTopOpcycleIso_hom
#print axioms LinearStudy.cochainActualTopOpcycleIso_hom
#check @LinearStudy.cochainActualTopCovariant_surjective
#print axioms LinearStudy.cochainActualTopCovariant_surjective
#check @LinearStudy.cochainActualTopCovariant_kernel
#print axioms LinearStudy.cochainActualTopCovariant_kernel
#print LinearStudy.cochainActualTopOpcycleIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainActualTopOpcycleIso,false),(`LinearStudy.cochainActualTopOpcycleIso_hom,true),(`LinearStudy.cochainActualTopCovariant_surjective,true),(`LinearStudy.cochainActualTopCovariant_kernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
