module
import all Linear.ProjectivePulledOriginalNamedChartObjects
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalNamedExactChart_ring
#print axioms LinearStudy.projectivePulledOriginalNamedExactChart_ring
#check @LinearStudy.projectivePulledOriginalNamedExactChart_inclusion
#print axioms LinearStudy.projectivePulledOriginalNamedExactChart_inclusion
#check @LinearStudy.projectivePulledOriginalNamedExactChart_awayInclusion
#print axioms LinearStudy.projectivePulledOriginalNamedExactChart_awayInclusion
#check @LinearStudy.projectivePulledOriginalAway_isOpenImmersion
#print axioms LinearStudy.projectivePulledOriginalAway_isOpenImmersion
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalNamedExactChart_ring,true),(`LinearStudy.projectivePulledOriginalNamedExactChart_inclusion,true),(`LinearStudy.projectivePulledOriginalNamedExactChart_awayInclusion,true),(`LinearStudy.projectivePulledOriginalAway_isOpenImmersion,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
