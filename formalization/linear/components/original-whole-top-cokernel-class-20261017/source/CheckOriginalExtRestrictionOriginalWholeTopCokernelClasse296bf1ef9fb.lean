module
import all Linear.SchemeModuleOriginalPositiveBoundaryIso
import all Linear.SchemeModuleOriginalNatTargetExt
import all Linear.SchemeModuleOriginalWholeTopCokernel
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalNatBoundaryStep_isIso
#print axioms LinearStudy.schemeModuleOriginalNatBoundaryStep_isIso
#check @LinearStudy.schemeModuleOriginalNatPositiveTail_isIso
#print axioms LinearStudy.schemeModuleOriginalNatPositiveTail_isIso
#check @LinearStudy.schemeModuleOriginalNatPositiveTailIso
#print axioms LinearStudy.schemeModuleOriginalNatPositiveTailIso
#check @LinearStudy.schemeModuleOriginalNatPositiveTailIso_hom
#print axioms LinearStudy.schemeModuleOriginalNatPositiveTailIso_hom
#check @LinearStudy.schemeModuleOriginalNatTargetExtIso
#print axioms LinearStudy.schemeModuleOriginalNatTargetExtIso
#check @LinearStudy.schemeModuleOriginalNatTargetExtIso_hom
#print axioms LinearStudy.schemeModuleOriginalNatTargetExtIso_hom
#check @LinearStudy.schemeModuleOriginalNatIteratedBoundary_factor
#print axioms LinearStudy.schemeModuleOriginalNatIteratedBoundary_factor
#check @LinearStudy.schemeModuleOriginalWholeTopCokernelIso
#print axioms LinearStudy.schemeModuleOriginalWholeTopCokernelIso
#check @LinearStudy.schemeModuleOriginalWholeTopCokernelIso_hom
#print axioms LinearStudy.schemeModuleOriginalWholeTopCokernelIso_hom
#check @LinearStudy.schemeModuleOriginalSmallClass_wholeTopCokernel
#print axioms LinearStudy.schemeModuleOriginalSmallClass_wholeTopCokernel
#print LinearStudy.schemeModuleOriginalNatPositiveTailIso
#print LinearStudy.schemeModuleOriginalNatTargetExtIso
#print LinearStudy.schemeModuleOriginalWholeTopCokernelIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalNatBoundaryStep_isIso,true),(`LinearStudy.schemeModuleOriginalNatPositiveTail_isIso,true),(`LinearStudy.schemeModuleOriginalNatPositiveTailIso,false),(`LinearStudy.schemeModuleOriginalNatPositiveTailIso_hom,true),(`LinearStudy.schemeModuleOriginalNatTargetExtIso,false),(`LinearStudy.schemeModuleOriginalNatTargetExtIso_hom,true),(`LinearStudy.schemeModuleOriginalNatIteratedBoundary_factor,true),(`LinearStudy.schemeModuleOriginalWholeTopCokernelIso,false),(`LinearStudy.schemeModuleOriginalWholeTopCokernelIso_hom,true),(`LinearStudy.schemeModuleOriginalSmallClass_wholeTopCokernel,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
