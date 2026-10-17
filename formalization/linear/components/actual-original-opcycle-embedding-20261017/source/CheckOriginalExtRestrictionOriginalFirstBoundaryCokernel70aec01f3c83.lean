module
import all Linear.SchemeModuleHomZeroBoundaryCokernel
import all Linear.SchemeModuleOriginalFirstBoundaryCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomZeroBoundary_cokernel
#print axioms LinearStudy.schemeModuleHomZeroBoundary_cokernel
#check @LinearStudy.schemeModuleOriginalFirstBoundary_cokernel
#print axioms LinearStudy.schemeModuleOriginalFirstBoundary_cokernel
#check @LinearStudy.schemeModuleOriginalAugmentedFirstBoundary_cokernel
#print axioms LinearStudy.schemeModuleOriginalAugmentedFirstBoundary_cokernel
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomZeroBoundary_cokernel,true),(`LinearStudy.schemeModuleOriginalFirstBoundary_cokernel,true),(`LinearStudy.schemeModuleOriginalAugmentedFirstBoundary_cokernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
