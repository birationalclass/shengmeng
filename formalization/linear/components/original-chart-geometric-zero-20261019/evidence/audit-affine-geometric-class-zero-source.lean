module
import all Linear.AffineKoszulGeometricClassZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulTopFunctionalSection
#print axioms LinearStudy.affineKoszulTopFunctionalSection
#check @LinearStudy.affineKoszulGeometricClass_eq_restriction
#print axioms LinearStudy.affineKoszulGeometricClass_eq_restriction
#check @LinearStudy.affineKoszulGeometricClass_zero_iff_pullback
#print axioms LinearStudy.affineKoszulGeometricClass_zero_iff_pullback
#print LinearStudy.affineKoszulTopFunctionalSection
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulTopFunctionalSection,false),(`LinearStudy.affineKoszulGeometricClass_eq_restriction,true),(`LinearStudy.affineKoszulGeometricClass_zero_iff_pullback,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
