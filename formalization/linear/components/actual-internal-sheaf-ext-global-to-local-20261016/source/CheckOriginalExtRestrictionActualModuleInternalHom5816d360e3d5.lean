module
import all Linear.AffineKoszulActualModuleExtInternalHomTop
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulActualModuleExtInternalHomTopIso
#print axioms LinearStudy.affineKoszulActualModuleExtInternalHomTopIso
#check @LinearStudy.affineKoszulActualInternalHomCyclesToModuleExt
#print axioms LinearStudy.affineKoszulActualInternalHomCyclesToModuleExt
#check @LinearStudy.affineKoszulActualModuleExtInternalHomTopIso_cycles
#print axioms LinearStudy.affineKoszulActualModuleExtInternalHomTopIso_cycles
#print LinearStudy.affineKoszulActualModuleExtInternalHomTopIso
#print LinearStudy.affineKoszulActualInternalHomCyclesToModuleExt
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulActualModuleExtInternalHomTopIso,false),(`LinearStudy.affineKoszulActualInternalHomCyclesToModuleExt,false),(`LinearStudy.affineKoszulActualModuleExtInternalHomTopIso_cycles,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
