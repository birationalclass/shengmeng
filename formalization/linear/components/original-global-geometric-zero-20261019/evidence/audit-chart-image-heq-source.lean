module
import all Linear.SchemeModuleChartImageHEq
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.scheme_chart_image_top_eq_of_HEq
#print axioms LinearStudy.scheme_chart_image_top_eq_of_HEq
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.scheme_chart_image_top_eq_of_HEq,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
