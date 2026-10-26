module
import all Linear.AffineKoszulActualSheafExtNativeDirectValues
import all Linear.OriginalCutEquationActualSheafExtNativeStatement
import all Linear.OriginalCutEquationActualSheafExtNativeDuality
import all Linear.OriginalCutEquationActualSheafExtNativeSetup
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement
#print axioms LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement
#check @LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement_of_coefficient
#print axioms LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement_of_coefficient
#check @LinearStudy.projectivePulledCutEquationActualSheafExtNativeStatement
#print axioms LinearStudy.projectivePulledCutEquationActualSheafExtNativeStatement
#check @LinearStudy.projectivePulledCutEquation_actualSheafExt_native_of_duality
#print axioms LinearStudy.projectivePulledCutEquation_actualSheafExt_native_of_duality
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExt_native_values_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExt_native_values_open
#print LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement
#print LinearStudy.projectivePulledCutEquationActualSheafExtNativeStatement
#print LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement
#print axioms LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement
#print LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
#print axioms LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement,false),(`LinearStudy.affineKoszulActualSheafExtNativeDirectValuesStatement_of_coefficient,true),(`LinearStudy.projectivePulledCutEquationActualSheafExtNativeStatement,false),(`LinearStudy.projectivePulledCutEquation_actualSheafExt_native_of_duality,true),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExt_native_values_open,true)]
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
