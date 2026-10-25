module
import all Linear.PolynomialPointOriginalFiberDual
import all Linear.SurjectiveBaseFiberQuotient
import all Linear.OriginalCutEquationTensorFiber
import all Linear.OriginalCutEquationCoefficientFiberDual
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.polynomial_point_original_fiber_dual_exists
#print axioms LinearStudy.polynomial_point_original_fiber_dual_exists
#check @LinearStudy.surjectiveBaseFiberQuotientAlgEquiv
#print axioms LinearStudy.surjectiveBaseFiberQuotientAlgEquiv
#check @LinearStudy.surjectiveBaseFiberQuotientAlgEquiv_mk
#print axioms LinearStudy.surjectiveBaseFiberQuotientAlgEquiv_mk
#check @LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv
#print axioms LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv
#check @LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv_mk
#print axioms LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv_mk
#check @LinearStudy.projectivePulledCutEquationMap_zero_fiber_ideal
#print axioms LinearStudy.projectivePulledCutEquationMap_zero_fiber_ideal
#check @LinearStudy.projectivePulledCutEquationTensorFiberEquiv
#print axioms LinearStudy.projectivePulledCutEquationTensorFiberEquiv
#check @LinearStudy.projectivePulledCutEquationTensorFiberEquiv_tmul
#print axioms LinearStudy.projectivePulledCutEquationTensorFiberEquiv_tmul
#check @LinearStudy.projectivePulledCutEquationCoefficientFiberDualStatement
#print axioms LinearStudy.projectivePulledCutEquationCoefficientFiberDualStatement
#check @LinearStudy.projectivePulledCutEquation_coefficient_fiber_dual_of_smooth_cut
#print axioms LinearStudy.projectivePulledCutEquation_coefficient_fiber_dual_of_smooth_cut
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_dual_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_dual_open
#print LinearStudy.surjectiveBaseFiberQuotientAlgEquiv
#print LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv
#print LinearStudy.projectivePulledCutEquationTensorFiberEquiv
#print LinearStudy.projectivePulledCutEquationCoefficientFiberDualStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.polynomial_point_original_fiber_dual_exists,true),(`LinearStudy.surjectiveBaseFiberQuotientAlgEquiv,false),(`LinearStudy.surjectiveBaseFiberQuotientAlgEquiv_mk,true),(`LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv,false),(`LinearStudy.surjectiveBaseFiberQuotientOriginalFieldEquiv_mk,true),(`LinearStudy.projectivePulledCutEquationMap_zero_fiber_ideal,true),(`LinearStudy.projectivePulledCutEquationTensorFiberEquiv,false),(`LinearStudy.projectivePulledCutEquationTensorFiberEquiv_tmul,true),(`LinearStudy.projectivePulledCutEquationCoefficientFiberDualStatement,false),(`LinearStudy.projectivePulledCutEquation_coefficient_fiber_dual_of_smooth_cut,true),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_dual_open,true)]
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
