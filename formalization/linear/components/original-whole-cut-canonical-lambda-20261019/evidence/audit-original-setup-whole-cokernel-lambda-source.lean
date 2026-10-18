module
import all Linear.ParameterPolynomialFamilyIntersection
import all Linear.ProjectivePulledOriginalSetupWholeTopCokernelLambdaFamily
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.parameterPolynomialFamily_intersection
#print axioms LinearStudy.parameterPolynomialFamily_intersection
#check @LinearStudy.projectivePulledOriginalSetupWholeTopCokernelLambdaFamilyProof
#print axioms LinearStudy.projectivePulledOriginalSetupWholeTopCokernelLambdaFamilyProof
#print LinearStudy.projectivePulledOriginalSetupWholeTopCokernelLambdaFamilyProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.parameterPolynomialFamily_intersection,true),(`LinearStudy.projectivePulledOriginalSetupWholeTopCokernelLambdaFamilyProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
