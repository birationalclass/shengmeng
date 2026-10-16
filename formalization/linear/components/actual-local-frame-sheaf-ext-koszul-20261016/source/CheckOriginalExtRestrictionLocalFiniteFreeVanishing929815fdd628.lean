module
import all Linear.SchemeModuleFreeOverIso
import all Linear.SchemeModuleZeroFromOpenCover
import all Linear.SchemeModuleFiniteLocallyFreeInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleFreeOverIso
#print axioms LinearStudy.schemeModuleFreeOverIso
#check @LinearStudy.schemeModule_isZero_of_over_cover
#print axioms LinearStudy.schemeModule_isZero_of_over_cover
#check @LinearStudy.schemeModuleLocalFiniteFreeInternalExt_succ
#print axioms LinearStudy.schemeModuleLocalFiniteFreeInternalExt_succ
#check @LinearStudy.schemeModuleFiniteLocallyFreeInternalExt_succ_of_cover
#print axioms LinearStudy.schemeModuleFiniteLocallyFreeInternalExt_succ_of_cover
#print LinearStudy.schemeModuleFreeOverIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleFreeOverIso,false),(`LinearStudy.schemeModule_isZero_of_over_cover,true),(`LinearStudy.schemeModuleLocalFiniteFreeInternalExt_succ,true),(`LinearStudy.schemeModuleFiniteLocallyFreeInternalExt_succ_of_cover,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
