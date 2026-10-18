module
import all Linear.SchemeModuleChainOpenKoszulHomCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpenKoszulTermIso
#print axioms LinearStudy.schemeModuleChainOpenKoszulTermIso
#check @LinearStudy.schemeModuleChainOpenKoszulTermIso_differential
#print axioms LinearStudy.schemeModuleChainOpenKoszulTermIso_differential
#check @LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso
#print axioms LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso
#check @LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso_class
#print axioms LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso_class
#print LinearStudy.schemeModuleChainOpenKoszulTermIso
#print LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpenKoszulTermIso,false),(`LinearStudy.schemeModuleChainOpenKoszulTermIso_differential,true),(`LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso,false),(`LinearStudy.schemeModuleChainOpenKoszulHomCokernelIso_class,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
