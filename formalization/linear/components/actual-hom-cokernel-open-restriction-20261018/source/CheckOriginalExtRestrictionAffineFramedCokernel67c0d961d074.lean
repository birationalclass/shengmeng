module
import all Linear.AffineKoszulFramedHomCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulFramedHomCokernelIso
#print axioms LinearStudy.affineKoszulFramedHomCokernelIso
#check @LinearStudy.affineKoszulFramedHomCokernelIso_projection
#print axioms LinearStudy.affineKoszulFramedHomCokernelIso_projection
#check @LinearStudy.affineKoszulFramedHomCokernelIso_class
#print axioms LinearStudy.affineKoszulFramedHomCokernelIso_class
#print LinearStudy.affineKoszulFramedHomCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulFramedHomCokernelIso,false),(`LinearStudy.affineKoszulFramedHomCokernelIso_projection,true),(`LinearStudy.affineKoszulFramedHomCokernelIso_class,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
