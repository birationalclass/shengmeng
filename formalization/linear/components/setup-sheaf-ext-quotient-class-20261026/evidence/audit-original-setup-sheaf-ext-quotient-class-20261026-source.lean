module
import all Linear.OriginalCutEquationActualSheafExtClass
import all Linear.AffineKoszulOriginalSheafExtQuotientClass
import all Linear.AffineKoszulActualSheafExtNativeValues
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement
#print axioms LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement
#check @LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement_of_exact
#print axioms LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement_of_exact
#check @LinearStudy.projectivePulledCutEquationActualSheafExtClassStatement
#print axioms LinearStudy.projectivePulledCutEquationActualSheafExtClassStatement
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExtClass_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExtClass_open
#check @LinearStudy.affineKoszulOriginalTopCoefficientQuotientMap
#print axioms LinearStudy.affineKoszulOriginalTopCoefficientQuotientMap
#check @LinearStudy.affineKoszulHomCoefficientRestriction_eq_originalQuotient
#print axioms LinearStudy.affineKoszulHomCoefficientRestriction_eq_originalQuotient
#check @LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso
#print axioms LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso
#check @LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso_restriction
#print axioms LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso_restriction
#check @LinearStudy.affineKoszulOriginalSheafExtTensorIso
#print axioms LinearStudy.affineKoszulOriginalSheafExtTensorIso
#check @LinearStudy.affineKoszulOriginalSheafExtTensorIso_classLaw
#print axioms LinearStudy.affineKoszulOriginalSheafExtTensorIso_classLaw
#check @LinearStudy.affineKoszulOriginalSheafExtQuotientIso
#print axioms LinearStudy.affineKoszulOriginalSheafExtQuotientIso
#check @LinearStudy.affineKoszulOriginalSheafExtQuotientIso_classLaw
#print axioms LinearStudy.affineKoszulOriginalSheafExtQuotientIso_classLaw
#check @LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement
#print axioms LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement
#check @LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement_of_coefficient
#print axioms LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement_of_coefficient
#print LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement
#print LinearStudy.projectivePulledCutEquationActualSheafExtClassStatement
#print LinearStudy.affineKoszulOriginalTopCoefficientQuotientMap
#print LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso
#print LinearStudy.affineKoszulOriginalSheafExtTensorIso
#print LinearStudy.affineKoszulOriginalSheafExtQuotientIso
#print LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement
#print LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
#print axioms LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement,false),(`LinearStudy.affineKoszulOriginalSheafExtAllCoefficientsClassStatement_of_exact,true),(`LinearStudy.projectivePulledCutEquationActualSheafExtClassStatement,false),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_actualSheafExtClass_open,true),(`LinearStudy.affineKoszulOriginalTopCoefficientQuotientMap,false),(`LinearStudy.affineKoszulHomCoefficientRestriction_eq_originalQuotient,true),(`LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso,false),(`LinearStudy.affineKoszulOriginalCoefficientTensorGeometricIso_restriction,true),(`LinearStudy.affineKoszulOriginalSheafExtTensorIso,false),(`LinearStudy.affineKoszulOriginalSheafExtTensorIso_classLaw,true),(`LinearStudy.affineKoszulOriginalSheafExtQuotientIso,false),(`LinearStudy.affineKoszulOriginalSheafExtQuotientIso_classLaw,true),(`LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement,false),(`LinearStudy.affineKoszulActualSheafExtNativeTwoValuesStatement_of_coefficient,true)]
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
