module
import all Linear.NativeLocalizedSourcePoint
import all Linear.NativeLocalizedSourceFiberPoints
import all Linear.NativeLocalizedSourceReducedFiber
import all Linear.PolynomialPointOriginalLocalTrace
import all Linear.PolynomialPointOriginalFiberTrace
import all Linear.FiniteReducedRegularPointLocalData
import all Linear.ProjectiveSmoothCutPointLocalData
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeLocalizedSourcePointEquiv
#print axioms LinearStudy.nativeLocalizedSourcePointEquiv
#check @LinearStudy.nativeLocalizedSourcePointEquiv_numerator
#print axioms LinearStudy.nativeLocalizedSourcePointEquiv_numerator
#check @LinearStudy.nativeLocalizedSourcePoint_ringKrullDim
#print axioms LinearStudy.nativeLocalizedSourcePoint_ringKrullDim
#check @LinearStudy.nativeLocalizedSourcePoint_localCM
#print axioms LinearStudy.nativeLocalizedSourcePoint_localCM
#check @LinearStudy.nativeLocalizedSourcePoint_base_comap
#print axioms LinearStudy.nativeLocalizedSourcePoint_base_comap
#check @LinearStudy.nativeLocalizedSourcePoint_original_maximal
#print axioms LinearStudy.nativeLocalizedSourcePoint_original_maximal
#check @LinearStudy.nativeLocalizedSourceClosedFiber_reduced
#print axioms LinearStudy.nativeLocalizedSourceClosedFiber_reduced
#check @LinearStudy.polynomial_point_original_coextension_trace_one_of_original_points
#print axioms LinearStudy.polynomial_point_original_coextension_trace_one_of_original_points
#check @LinearStudy.polynomial_point_original_coextension_trace_one_of_original_fiber
#print axioms LinearStudy.polynomial_point_original_coextension_trace_one_of_original_fiber
#check @LinearStudy.finite_reduced_regular_cut_point_local_data
#print axioms LinearStudy.finite_reduced_regular_cut_point_local_data
#check @LinearStudy.projectivePulledLinearSection_smooth_cut_point_local_data
#print axioms LinearStudy.projectivePulledLinearSection_smooth_cut_point_local_data
#print LinearStudy.nativeLocalizedSourcePointEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeLocalizedSourcePointEquiv,false),(`LinearStudy.nativeLocalizedSourcePointEquiv_numerator,true),(`LinearStudy.nativeLocalizedSourcePoint_ringKrullDim,true),(`LinearStudy.nativeLocalizedSourcePoint_localCM,true),(`LinearStudy.nativeLocalizedSourcePoint_base_comap,true),(`LinearStudy.nativeLocalizedSourcePoint_original_maximal,true),(`LinearStudy.nativeLocalizedSourceClosedFiber_reduced,true),(`LinearStudy.polynomial_point_original_coextension_trace_one_of_original_points,true),(`LinearStudy.polynomial_point_original_coextension_trace_one_of_original_fiber,true),(`LinearStudy.finite_reduced_regular_cut_point_local_data,true),(`LinearStudy.projectivePulledLinearSection_smooth_cut_point_local_data,true)]
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
