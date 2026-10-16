module
import all Linear.SchemeModuleFiniteFreeInternalExt
import all Linear.SchemeModuleFiniteFreeFrameInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleFiniteFreeInternalExt_succ
#print axioms LinearStudy.schemeModuleFiniteFreeInternalExt_succ
#check @LinearStudy.schemeModuleInternalExtSourceIso
#print axioms LinearStudy.schemeModuleInternalExtSourceIso
#check @LinearStudy.schemeModuleFiniteFreeFrameInternalExt_succ
#print axioms LinearStudy.schemeModuleFiniteFreeFrameInternalExt_succ
#print LinearStudy.schemeModuleInternalExtSourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleFiniteFreeInternalExt_succ,true),(`LinearStudy.schemeModuleInternalExtSourceIso,false),(`LinearStudy.schemeModuleFiniteFreeFrameInternalExt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
