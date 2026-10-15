module
import all Linear.SchemeModuleDerivedInternalHom
import all Linear.SchemeModuleInternalExtZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtFunctor
#print axioms LinearStudy.schemeModuleInternalExtFunctor
#check @LinearStudy.schemeModuleInternalExt
#print axioms LinearStudy.schemeModuleInternalExt
#check @LinearStudy.schemeModuleInternalExtInjectiveResolutionIso
#print axioms LinearStudy.schemeModuleInternalExtInjectiveResolutionIso
#check @LinearStudy.schemeModuleInternalExt_injective_succ
#print axioms LinearStudy.schemeModuleInternalExt_injective_succ
#check @LinearStudy.schemeModuleInternalExtInjectiveResolutionIso_naturality
#print axioms LinearStudy.schemeModuleInternalExtInjectiveResolutionIso_naturality
#check @LinearStudy.schemeModuleInternalExtZeroIso
#print axioms LinearStudy.schemeModuleInternalExtZeroIso
#check @LinearStudy.schemeModuleInternalExtZeroIso_naturality
#print axioms LinearStudy.schemeModuleInternalExtZeroIso_naturality
#check @LinearStudy.schemeModuleInternalExtZeroIso_inv_app
#print axioms LinearStudy.schemeModuleInternalExtZeroIso_inv_app
#check @LinearStudy.schemeModuleInternalExtZeroSectionEquiv
#print axioms LinearStudy.schemeModuleInternalExtZeroSectionEquiv
#print LinearStudy.schemeModuleInternalExtFunctor
#print LinearStudy.schemeModuleInternalExt
#print LinearStudy.schemeModuleInternalExtInjectiveResolutionIso
#print LinearStudy.schemeModuleInternalExtZeroIso
#print LinearStudy.schemeModuleInternalExtZeroSectionEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtFunctor,false),(`LinearStudy.schemeModuleInternalExt,false),(`LinearStudy.schemeModuleInternalExtInjectiveResolutionIso,false),(`LinearStudy.schemeModuleInternalExt_injective_succ,true),(`LinearStudy.schemeModuleInternalExtInjectiveResolutionIso_naturality,true),(`LinearStudy.schemeModuleInternalExtZeroIso,false),(`LinearStudy.schemeModuleInternalExtZeroIso_naturality,true),(`LinearStudy.schemeModuleInternalExtZeroIso_inv_app,true),(`LinearStudy.schemeModuleInternalExtZeroSectionEquiv,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
