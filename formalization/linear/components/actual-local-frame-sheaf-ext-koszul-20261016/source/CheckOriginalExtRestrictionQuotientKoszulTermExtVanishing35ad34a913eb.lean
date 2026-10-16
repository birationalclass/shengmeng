module
import all Linear.HomogeneousQuotientKoszulTermInternalExtVanishing
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.homogeneousQuotientCoordinate_adjoin_eq_top
#print axioms LinearStudy.homogeneousQuotientCoordinate_adjoin_eq_top
#check @LinearStudy.homogeneousQuotientKoszulTermInternalExt_succ
#print axioms LinearStudy.homogeneousQuotientKoszulTermInternalExt_succ
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.homogeneousQuotientCoordinate_adjoin_eq_top,true),(`LinearStudy.homogeneousQuotientKoszulTermInternalExt_succ,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
