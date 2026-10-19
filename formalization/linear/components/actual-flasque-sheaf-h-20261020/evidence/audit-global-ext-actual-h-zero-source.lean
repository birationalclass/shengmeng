module
import all Linear.ExtZeroHomCoefficientNaturality
import all Linear.SchemeModuleGlobalExtActualHZero
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.extZeroHomEquiv_postcompose
#print axioms LinearStudy.extZeroHomEquiv_postcompose
#check @LinearStudy.schemeModuleUnitHomGlobalSectionsAddEquiv
#print axioms LinearStudy.schemeModuleUnitHomGlobalSectionsAddEquiv
#check @LinearStudy.schemeModuleGlobalExtZeroSectionsAddEquiv
#print axioms LinearStudy.schemeModuleGlobalExtZeroSectionsAddEquiv
#check @LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv
#print axioms LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv
#check @LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_evaluate
#print axioms LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_evaluate
#check @LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_naturality
#print axioms LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_naturality
#print LinearStudy.schemeModuleUnitHomGlobalSectionsAddEquiv
#print LinearStudy.schemeModuleGlobalExtZeroSectionsAddEquiv
#print LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.extZeroHomEquiv_postcompose,true),(`LinearStudy.schemeModuleUnitHomGlobalSectionsAddEquiv,false),(`LinearStudy.schemeModuleGlobalExtZeroSectionsAddEquiv,false),(`LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv,false),(`LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_evaluate,true),(`LinearStudy.schemeModuleGlobalExtZeroActualHAddEquiv_naturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
