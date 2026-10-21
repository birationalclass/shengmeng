module
import all Linear.SchemeModuleActualHSpecScalars
import all Linear.CoordinateNativeCechHomologyModel
import all Linear.NativeNormalizationActualHKLinearIso
import all Linear.NativeSpecifiedNormalizationTopDualityKLinearIso
import all Linear.NativeSpecifiedNormalizationTopDualityKForget
import all Linear.NativeSpecifiedNormalizationTopDualityScalar
import all Linear.NativeSpecifiedNormalizationTopPairing
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleActualHSpecModule
#print axioms LinearStudy.schemeModuleActualHSpecModule
#check @LinearStudy.schemeModuleActualHSpecModule_smul
#print axioms LinearStudy.schemeModuleActualHSpecModule_smul
#check @LinearStudy.schemeModuleActualHSpecLinearCoefficientMap
#print axioms LinearStudy.schemeModuleActualHSpecLinearCoefficientMap
#check @LinearStudy.schemeModuleActualHSpecLinearCoefficientMap_apply
#print axioms LinearStudy.schemeModuleActualHSpecLinearCoefficientMap_apply
#check @MvPolynomial.coordinateNativeCechHomologyFunctorModelIso
#print axioms MvPolynomial.coordinateNativeCechHomologyFunctorModelIso
#check @MvPolynomial.coordinateNativeCechHomologyFunctorModelIso_apply
#print axioms MvPolynomial.coordinateNativeCechHomologyFunctorModelIso_apply
#check @LinearStudy.nativeFiniteNormalization_moduleCechActualHigherHKLinearIso
#print axioms LinearStudy.nativeFiniteNormalization_moduleCechActualHigherHKLinearIso
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_forget
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_forget
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_scalarPairing
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_scalarPairing
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_left_nondegenerate
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_left_nondegenerate
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_right_nondegenerate
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_right_nondegenerate
#print LinearStudy.schemeModuleActualHSpecModule
#print LinearStudy.schemeModuleActualHSpecLinearCoefficientMap
#print MvPolynomial.coordinateNativeCechHomologyFunctorModelIso
#print LinearStudy.nativeFiniteNormalization_moduleCechActualHigherHKLinearIso
#print LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleActualHSpecModule,false),(`LinearStudy.schemeModuleActualHSpecModule_smul,true),(`LinearStudy.schemeModuleActualHSpecLinearCoefficientMap,false),(`LinearStudy.schemeModuleActualHSpecLinearCoefficientMap_apply,true),(`MvPolynomial.coordinateNativeCechHomologyFunctorModelIso,false),(`MvPolynomial.coordinateNativeCechHomologyFunctorModelIso_apply,true),(`LinearStudy.nativeFiniteNormalization_moduleCechActualHigherHKLinearIso,false),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso,false),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_forget,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_scalarPairing,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_left_nondegenerate,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_right_nondegenerate,true)]
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
