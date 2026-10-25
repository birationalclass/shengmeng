module
import all Linear.HomogeneousQuotientRelation
import all Linear.HomogeneousQuotientMapFinite
import all Linear.HomogeneousNoBasePointFinite
import all Linear.HomogeneousConeAffineFinite
import all Linear.HomogeneousCutAffineFinite
import all Linear.OriginalCutEquationZeroFiber
import all Linear.ProjectiveAffineMaximalPoint
import all Linear.ProjectiveCutEquationMapFinite
import all Linear.ProjectiveCutEquationFiberLocalData
import all Linear.ProjectiveCutEquationPointTrace
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.homogeneous_quotient_bounded_relation
#print axioms LinearStudy.homogeneous_quotient_bounded_relation
#check @LinearStudy.homogeneous_quotient_polynomial_map_finite_of_origin_zeroLocus
#print axioms LinearStudy.homogeneous_quotient_polynomial_map_finite_of_origin_zeroLocus
#check @LinearStudy.homogeneous_quotient_map_finite_of_no_base_points
#print axioms LinearStudy.homogeneous_quotient_map_finite_of_no_base_points
#check @LinearStudy.homogeneous_cone_finite_implies_actual_affine_map_finite
#print axioms LinearStudy.homogeneous_cone_finite_implies_actual_affine_map_finite
#check @LinearStudy.homogeneous_cut_no_infinity_actual_affine_map_finite
#print axioms LinearStudy.homogeneous_cut_no_infinity_actual_affine_map_finite
#check @LinearStudy.polynomial_equation_zero_fiber_ideal
#print axioms LinearStudy.polynomial_equation_zero_fiber_ideal
#check @LinearStudy.projectivePulledCutEquation_zero_fiber_reduced
#print axioms LinearStudy.projectivePulledCutEquation_zero_fiber_reduced
#check @LinearStudy.projectivePulledCutEquation_zero_fiber_finite
#print axioms LinearStudy.projectivePulledCutEquation_zero_fiber_finite
#check @LinearStudy.IntegralProjectiveEquations.affineMaximal_point
#print axioms LinearStudy.IntegralProjectiveEquations.affineMaximal_point
#check @LinearStudy.projectivePulledCutEquationMap
#print axioms LinearStudy.projectivePulledCutEquationMap
#check @LinearStudy.projectivePulledCutEquationMap_finite_of_original_no_infinity
#print axioms LinearStudy.projectivePulledCutEquationMap_finite_of_original_no_infinity
#check @LinearStudy.projectivePulledCutEquationMap_exists_finite_open
#print axioms LinearStudy.projectivePulledCutEquationMap_exists_finite_open
#check @LinearStudy.projectivePulledCutEquation_zeroFiber_original_point
#print axioms LinearStudy.projectivePulledCutEquation_zeroFiber_original_point
#check @LinearStudy.projectivePulledCutEquation_zeroFiber_all_point_local_data
#print axioms LinearStudy.projectivePulledCutEquation_zeroFiber_all_point_local_data
#check @LinearStudy.projectivePulledCutEquationTraceOneStatement
#print axioms LinearStudy.projectivePulledCutEquationTraceOneStatement
#check @LinearStudy.projectivePulledCutEquation_trace_one_of_original_smooth_cut
#print axioms LinearStudy.projectivePulledCutEquation_trace_one_of_original_smooth_cut
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_trace_one_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_trace_one_open
#print LinearStudy.projectivePulledCutEquationMap
#print LinearStudy.projectivePulledCutEquationTraceOneStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.homogeneous_quotient_bounded_relation,true),(`LinearStudy.homogeneous_quotient_polynomial_map_finite_of_origin_zeroLocus,true),(`LinearStudy.homogeneous_quotient_map_finite_of_no_base_points,true),(`LinearStudy.homogeneous_cone_finite_implies_actual_affine_map_finite,true),(`LinearStudy.homogeneous_cut_no_infinity_actual_affine_map_finite,true),(`LinearStudy.polynomial_equation_zero_fiber_ideal,true),(`LinearStudy.projectivePulledCutEquation_zero_fiber_reduced,true),(`LinearStudy.projectivePulledCutEquation_zero_fiber_finite,true),(`LinearStudy.IntegralProjectiveEquations.affineMaximal_point,true),(`LinearStudy.projectivePulledCutEquationMap,false),(`LinearStudy.projectivePulledCutEquationMap_finite_of_original_no_infinity,true),(`LinearStudy.projectivePulledCutEquationMap_exists_finite_open,true),(`LinearStudy.projectivePulledCutEquation_zeroFiber_original_point,true),(`LinearStudy.projectivePulledCutEquation_zeroFiber_all_point_local_data,true),(`LinearStudy.projectivePulledCutEquationTraceOneStatement,false),(`LinearStudy.projectivePulledCutEquation_trace_one_of_original_smooth_cut,true),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_trace_one_open,true)]
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
