module
import all Linear.SchemeModuleInternalExtOpenSupport
import all Linear.SchemeModuleInternalExtSupportedUnit
import all Linear.SchemeModuleGlobalExtOpenZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExt_open_isZero_of_source
#print axioms LinearStudy.schemeModuleInternalExt_open_isZero_of_source
#check @LinearStudy.schemeModuleInternalExt_restrictionUnit_isIso_of_originalCover
#print axioms LinearStudy.schemeModuleInternalExt_restrictionUnit_isIso_of_originalCover
#check @LinearStudy.schemeModule_morphism_zero_iff_restrict_of_target_unit_isIso
#print axioms LinearStudy.schemeModule_morphism_zero_iff_restrict_of_target_unit_isIso
#check @LinearStudy.schemeModuleGlobalExt_zero_iff_open
#print axioms LinearStudy.schemeModuleGlobalExt_zero_iff_open
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExt_open_isZero_of_source,true),(`LinearStudy.schemeModuleInternalExt_restrictionUnit_isIso_of_originalCover,true),(`LinearStudy.schemeModule_morphism_zero_iff_restrict_of_target_unit_isIso,true),(`LinearStudy.schemeModuleGlobalExt_zero_iff_open,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
