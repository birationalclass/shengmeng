module
import all Linear.IntegerGradedEndZero
import all Linear.CoextensionDegreeZeroEndEvaluation
import all Linear.CoextensionDegreeZeroRigidity
import all Linear.NativeCoextensionSpecifiedTraceProperties
import all Linear.NativeCoextensionSpecifiedTraceInjective
import all Linear.NativeCoextensionSpecifiedTraceScalarRigidity
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.integerGradedEndZero
#print axioms LinearStudy.integerGradedEndZero
#check @LinearStudy.embeddedDomainModule_nonzero_end_injective
#print axioms LinearStudy.embeddedDomainModule_nonzero_end_injective
#check @LinearStudy.integerGradedEndZero_noZeroDivisors
#print axioms LinearStudy.integerGradedEndZero_noZeroDivisors
#check @LinearStudy.coextensionDegreeZeroEndEvaluation
#print axioms LinearStudy.coextensionDegreeZeroEndEvaluation
#check @LinearStudy.coextensionDegreeZeroEndEvaluation_injective
#print axioms LinearStudy.coextensionDegreeZeroEndEvaluation_injective
#check @LinearStudy.coextensionDegreeZeroEnd_finite
#print axioms LinearStudy.coextensionDegreeZeroEnd_finite
#check @LinearStudy.coextensionDegreeZeroEndEvaluation_surjective
#print axioms LinearStudy.coextensionDegreeZeroEndEvaluation_surjective
#check @LinearStudy.coextensionDegreeZeroEnd_exists_scalar
#print axioms LinearStudy.coextensionDegreeZeroEnd_exists_scalar
#check @LinearStudy.coextensionDegreeZeroHom_exists_scalar_evaluation
#print axioms LinearStudy.coextensionDegreeZeroHom_exists_scalar_evaluation
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom_ne_zero
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom_ne_zero
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_exists_one
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_exists_one
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_injective
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_injective
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_surjective
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_surjective
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_bijective
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_bijective
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_nonzero_scalar_transfer
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_nonzero_scalar_transfer
#print LinearStudy.integerGradedEndZero
#print LinearStudy.coextensionDegreeZeroEndEvaluation
#print LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom
#print LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace
#print LinearStudy.coextensionOriginalAdjoint
#print axioms LinearStudy.coextensionOriginalAdjoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.integerGradedEndZero,false),(`LinearStudy.embeddedDomainModule_nonzero_end_injective,true),(`LinearStudy.integerGradedEndZero_noZeroDivisors,true),(`LinearStudy.coextensionDegreeZeroEndEvaluation,false),(`LinearStudy.coextensionDegreeZeroEndEvaluation_injective,true),(`LinearStudy.coextensionDegreeZeroEnd_finite,true),(`LinearStudy.coextensionDegreeZeroEndEvaluation_surjective,true),(`LinearStudy.coextensionDegreeZeroEnd_exists_scalar,true),(`LinearStudy.coextensionDegreeZeroHom_exists_scalar_evaluation,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom_ne_zero,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_exists_one,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_injective,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_surjective,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_bijective,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_nonzero_scalar_transfer,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if want then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
