module
import all Linear.SchemeModuleUnitHomSections
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOverSectionsEquiv
#print axioms LinearStudy.schemeModuleOverSectionsEquiv
#check @LinearStudy.schemeModuleUnitOverIso
#print axioms LinearStudy.schemeModuleUnitOverIso
#check @LinearStudy.schemeModuleUnitHomSectionsEquiv
#print axioms LinearStudy.schemeModuleUnitHomSectionsEquiv
#check @LinearStudy.schemeModuleUnitHomSectionsEquiv_apply
#print axioms LinearStudy.schemeModuleUnitHomSectionsEquiv_apply
#print LinearStudy.schemeModuleOverSectionsEquiv
#print LinearStudy.schemeModuleUnitOverIso
#print LinearStudy.schemeModuleUnitHomSectionsEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOverSectionsEquiv,false),(`LinearStudy.schemeModuleUnitOverIso,false),(`LinearStudy.schemeModuleUnitHomSectionsEquiv,false),(`LinearStudy.schemeModuleUnitHomSectionsEquiv_apply,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
