module
import all Linear.SchemeModuleHomUnitFrameZero
import all Linear.AffineKoszulIntrinsicPullbackZero
import all Linear.SchemeModuleOpenKoszulIntrinsicZero
import all Linear.ProjectivePulledOriginalChartIntrinsicMapZero
import all Linear.SchemeModuleOriginalKoszulPushIntrinsicZero
import all Linear.ProjectivePulledOriginalSetupIntrinsicZeroFamily
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleUnitHomIso_curry
#print axioms LinearStudy.schemeModuleUnitHomIso_curry
#check @LinearStudy.schemeModuleLineFrameHomIso
#print axioms LinearStudy.schemeModuleLineFrameHomIso
#check @LinearStudy.schemeModuleLineFrameHomIso_hom
#print axioms LinearStudy.schemeModuleLineFrameHomIso_hom
#check @LinearStudy.schemeModuleLineFrameHomIso_curry
#print axioms LinearStudy.schemeModuleLineFrameHomIso_curry
#check @LinearStudy.schemeModuleLineFrame_curry_map_zero_iff
#print axioms LinearStudy.schemeModuleLineFrame_curry_map_zero_iff
#check @LinearStudy.affineKoszulTopFunctionalSection_pullback_zero_iff
#print axioms LinearStudy.affineKoszulTopFunctionalSection_pullback_zero_iff
#check @LinearStudy.affineKoszulGeometricClass_zero_iff_pullback_functional
#print axioms LinearStudy.affineKoszulGeometricClass_zero_iff_pullback_functional
#check @LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroStatement
#print axioms LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroStatement
#check @LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroProof
#print axioms LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroProof
#check @LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement
#print axioms LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement
#check @LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement_proof
#print axioms LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement_proof
#check @LinearStudy.schemeModuleOriginalKoszulPush_intrinsic_zero_iff
#print axioms LinearStudy.schemeModuleOriginalKoszulPush_intrinsic_zero_iff
#check @LinearStudy.projectivePulledOriginalSetupIntrinsicZeroFamilyProof
#print axioms LinearStudy.projectivePulledOriginalSetupIntrinsicZeroFamilyProof
#print LinearStudy.schemeModuleLineFrameHomIso
#print LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroStatement
#print LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement
#print LinearStudy.schemeModuleOriginalChainTopExtClassSmall
#print axioms LinearStudy.schemeModuleOriginalChainTopExtClassSmall
#print LinearStudy.affineKoszulTopFunctionalSection
#print axioms LinearStudy.affineKoszulTopFunctionalSection
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleUnitHomIso_curry,true),(`LinearStudy.schemeModuleLineFrameHomIso,false),(`LinearStudy.schemeModuleLineFrameHomIso_hom,true),(`LinearStudy.schemeModuleLineFrameHomIso_curry,true),(`LinearStudy.schemeModuleLineFrame_curry_map_zero_iff,true),(`LinearStudy.affineKoszulTopFunctionalSection_pullback_zero_iff,true),(`LinearStudy.affineKoszulGeometricClass_zero_iff_pullback_functional,true),(`LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroStatement,false),(`LinearStudy.schemeModuleOpenKoszulIntrinsicMapZeroProof,true),(`LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement,false),(`LinearStudy.projectivePulledOriginalChartIntrinsicMapZeroStatement_proof,true),(`LinearStudy.schemeModuleOriginalKoszulPush_intrinsic_zero_iff,true),(`LinearStudy.projectivePulledOriginalSetupIntrinsicZeroFamilyProof,true)]
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
