module
import all Linear.AffineKoszulHomGeometricCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulHomGeometricCokernelIso
#print axioms LinearStudy.affineKoszulHomGeometricCokernelIso
#check @LinearStudy.affineKoszulHomGeometricCokernelIso_projection
#print axioms LinearStudy.affineKoszulHomGeometricCokernelIso_projection
#print LinearStudy.affineKoszulHomGeometricCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulHomGeometricCokernelIso,false),(`LinearStudy.affineKoszulHomGeometricCokernelIso_projection,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
