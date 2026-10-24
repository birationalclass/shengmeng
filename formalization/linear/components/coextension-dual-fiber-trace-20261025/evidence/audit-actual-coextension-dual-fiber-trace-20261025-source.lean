module
import all Linear.CoextensionFieldPointTrace
import all Linear.CoextensionOriginalDualTensorBaseChange
import all Linear.CoextensionOriginalFiberPointProjector
import all Linear.CoextensionResidueFiberPointProjector
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.coextensionFieldTrace_nonzero_element_exists_one
#print axioms LinearStudy.coextensionFieldTrace_nonzero_element_exists_one
#check @LinearStudy.coextensionFieldTrace_idempotent_fixed_exists_one
#print axioms LinearStudy.coextensionFieldTrace_idempotent_fixed_exists_one
#check @LinearStudy.coextensionOriginalDualTensorEquiv
#print axioms LinearStudy.coextensionOriginalDualTensorEquiv
#check @LinearStudy.coextensionOriginalDualTensorEquiv_tmul_apply
#print axioms LinearStudy.coextensionOriginalDualTensorEquiv_tmul_apply
#check @LinearStudy.coextensionOriginalDualTensorEquiv_original_evaluation
#print axioms LinearStudy.coextensionOriginalDualTensorEquiv_original_evaluation
#check @LinearStudy.coextensionOriginalScalarRLinear
#print axioms LinearStudy.coextensionOriginalScalarRLinear
#check @LinearStudy.coextensionOriginalScalarFiberEnd
#print axioms LinearStudy.coextensionOriginalScalarFiberEnd
#check @LinearStudy.coextensionOriginalFiberTrace
#print axioms LinearStudy.coextensionOriginalFiberTrace
#check @LinearStudy.coextensionOriginalDualTensorEquiv_both_tmul
#print axioms LinearStudy.coextensionOriginalDualTensorEquiv_both_tmul
#check @LinearStudy.coextensionOriginalDualTensorEquiv_scalar_naturality
#print axioms LinearStudy.coextensionOriginalDualTensorEquiv_scalar_naturality
#check @LinearStudy.coextensionOriginalScalarFiberEnd_idempotent
#print axioms LinearStudy.coextensionOriginalScalarFiberEnd_idempotent
#check @LinearStudy.coextensionOriginalFiberTrace_tmul
#print axioms LinearStudy.coextensionOriginalFiberTrace_tmul
#check @LinearStudy.coextensionOriginalFiberTrace_actual_point_exists_one
#print axioms LinearStudy.coextensionOriginalFiberTrace_actual_point_exists_one
#check @LinearStudy.coextensionOriginalScalarFiberEnd_eq_of_fiber_eq
#print axioms LinearStudy.coextensionOriginalScalarFiberEnd_eq_of_fiber_eq
#check @LinearStudy.coextensionOriginalResidueFiberPointEnd
#print axioms LinearStudy.coextensionOriginalResidueFiberPointEnd
#check @LinearStudy.coextensionOriginalResidueFiberPointEnd_of_lift
#print axioms LinearStudy.coextensionOriginalResidueFiberPointEnd_of_lift
#check @LinearStudy.coextensionOriginalResidueFiberPointEnd_idempotent
#print axioms LinearStudy.coextensionOriginalResidueFiberPointEnd_idempotent
#check @LinearStudy.coextensionOriginalResidueFiberPointTrace_exists_one
#print axioms LinearStudy.coextensionOriginalResidueFiberPointTrace_exists_one
#print LinearStudy.coextensionOriginalDualTensorEquiv
#print LinearStudy.coextensionOriginalScalarRLinear
#print LinearStudy.coextensionOriginalScalarFiberEnd
#print LinearStudy.coextensionOriginalFiberTrace
#print LinearStudy.coextensionOriginalResidueFiberPointEnd
#print LinearStudy.coextensionOriginalDualEquiv
#print axioms LinearStudy.coextensionOriginalDualEquiv
#print LinearStudy.coextensionOriginalEvaluationAtOne
#print axioms LinearStudy.coextensionOriginalEvaluationAtOne
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.coextensionFieldTrace_nonzero_element_exists_one,true),(`LinearStudy.coextensionFieldTrace_idempotent_fixed_exists_one,true),(`LinearStudy.coextensionOriginalDualTensorEquiv,false),(`LinearStudy.coextensionOriginalDualTensorEquiv_tmul_apply,true),(`LinearStudy.coextensionOriginalDualTensorEquiv_original_evaluation,true),(`LinearStudy.coextensionOriginalScalarRLinear,false),(`LinearStudy.coextensionOriginalScalarFiberEnd,false),(`LinearStudy.coextensionOriginalFiberTrace,false),(`LinearStudy.coextensionOriginalDualTensorEquiv_both_tmul,true),(`LinearStudy.coextensionOriginalDualTensorEquiv_scalar_naturality,true),(`LinearStudy.coextensionOriginalScalarFiberEnd_idempotent,true),(`LinearStudy.coextensionOriginalFiberTrace_tmul,true),(`LinearStudy.coextensionOriginalFiberTrace_actual_point_exists_one,true),(`LinearStudy.coextensionOriginalScalarFiberEnd_eq_of_fiber_eq,true),(`LinearStudy.coextensionOriginalResidueFiberPointEnd,false),(`LinearStudy.coextensionOriginalResidueFiberPointEnd_of_lift,true),(`LinearStudy.coextensionOriginalResidueFiberPointEnd_idempotent,true),(`LinearStudy.coextensionOriginalResidueFiberPointTrace_exists_one,true)]
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
