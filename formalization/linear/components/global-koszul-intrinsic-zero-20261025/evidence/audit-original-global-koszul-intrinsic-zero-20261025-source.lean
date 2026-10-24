module
import all Linear.ParameterFamilyProjectSharedWitness
import all Linear.SchemeModuleGlobalKoszulIntrinsicZero
import all Linear.ProjectivePulledOriginalGlobalIntrinsicZero
import all Linear.ProjectivePulledOriginalSetupGlobalIntrinsicFamily
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.parameterFamily_project_from_sharedFacts
#print axioms LinearStudy.parameterFamily_project_from_sharedFacts
#check @LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroStatement
#print axioms LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroStatement
#check @LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof
#print axioms LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof
#check @LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof_of_cokernelLambda
#print axioms LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof_of_cokernelLambda
#check @LinearStudy.schemeModuleOriginalKoszulPush_global_intrinsic_zero_iff
#print axioms LinearStudy.schemeModuleOriginalKoszulPush_global_intrinsic_zero_iff
#check @LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement
#print axioms LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement
#check @LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement_proof
#print axioms LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement_proof
#check @LinearStudy.projectivePulledOriginalSetupGlobalIntrinsicZeroFamilyProof
#print axioms LinearStudy.projectivePulledOriginalSetupGlobalIntrinsicZeroFamilyProof
#print LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroStatement
#print LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement
#print LinearStudy.schemeModuleOriginalChainTopExtClassSmall
#print axioms LinearStudy.schemeModuleOriginalChainTopExtClassSmall
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.parameterFamily_project_from_sharedFacts,true),(`LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroStatement,false),(`LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof,true),(`LinearStudy.schemeModuleGlobalKoszulIntrinsicZeroProof_of_cokernelLambda,true),(`LinearStudy.schemeModuleOriginalKoszulPush_global_intrinsic_zero_iff,true),(`LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement,false),(`LinearStudy.projectivePulledOriginalGlobalIntrinsicZeroStatement_proof,true),(`LinearStudy.projectivePulledOriginalSetupGlobalIntrinsicZeroFamilyProof,true)]
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
