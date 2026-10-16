module
import all Linear.SchemeModuleUnitHomIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleUnitHomSectionsLinearEquiv
#print axioms LinearStudy.schemeModuleUnitHomSectionsLinearEquiv
#check @LinearStudy.schemeModuleUnitHomSectionsEquiv_restrict
#print axioms LinearStudy.schemeModuleUnitHomSectionsEquiv_restrict
#check @LinearStudy.schemeModuleUnitHomIso
#print axioms LinearStudy.schemeModuleUnitHomIso
#check @LinearStudy.schemeModuleUnitHomIso_hom_app
#print axioms LinearStudy.schemeModuleUnitHomIso_hom_app
#check @LinearStudy.schemeModuleInternalHomUnitCoefficientIso
#print axioms LinearStudy.schemeModuleInternalHomUnitCoefficientIso
#print LinearStudy.schemeModuleUnitHomSectionsLinearEquiv
#print LinearStudy.schemeModuleUnitHomIso
#print LinearStudy.schemeModuleInternalHomUnitCoefficientIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleUnitHomSectionsLinearEquiv,false),(`LinearStudy.schemeModuleUnitHomSectionsEquiv_restrict,true),(`LinearStudy.schemeModuleUnitHomIso,false),(`LinearStudy.schemeModuleUnitHomIso_hom_app,true),(`LinearStudy.schemeModuleInternalHomUnitCoefficientIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
