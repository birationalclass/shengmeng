module
import all Linear.TildeKoszulSourceInternalExtAcyclic
import all Linear.AffineKoszulActualSheafExtTop
import all Linear.SchemeModuleOriginalTopExtClassIsoLaw
import all Linear.AffineKoszulOriginalSheafExtClass
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeOriginalBasisFreeFrame
#print axioms LinearStudy.tildeOriginalBasisFreeFrame
#check @LinearStudy.tildeFunctionKoszul_sourceInternalExtAcyclic
#print axioms LinearStudy.tildeFunctionKoszul_sourceInternalExtAcyclic
#check @LinearStudy.tildeFunctionKoszul_isZero_above_rank
#print axioms LinearStudy.tildeFunctionKoszul_isZero_above_rank
#check @LinearStudy.tildeKoszulActualCutCokernelIso
#print axioms LinearStudy.tildeKoszulActualCutCokernelIso
#check @LinearStudy.tildeKoszulActualCutCokernelIso_projection
#print axioms LinearStudy.tildeKoszulActualCutCokernelIso_projection
#check @LinearStudy.tildeKoszulActualCutCokernelAugmentation_eq_cofork
#print axioms LinearStudy.tildeKoszulActualCutCokernelAugmentation_eq_cofork
#check @LinearStudy.tildeKoszulActualCutCokernelAugmentation_quasiIso
#print axioms LinearStudy.tildeKoszulActualCutCokernelAugmentation_quasiIso
#check @LinearStudy.affineKoszulActualSheafExtTopHomologyIso
#print axioms LinearStudy.affineKoszulActualSheafExtTopHomologyIso
#check @LinearStudy.affineKoszulActualSheafExtTopModuleExtIso
#print axioms LinearStudy.affineKoszulActualSheafExtTopModuleExtIso
#check @LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
#print axioms LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
#check @LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_wholeCokernel
#print axioms LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_wholeCokernel
#check @LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_postcompose
#print axioms LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_postcompose
#check @LinearStudy.affineKoszulOriginalSheafExtCokernelIso
#print axioms LinearStudy.affineKoszulOriginalSheafExtCokernelIso
#check @LinearStudy.affineKoszulOriginalSheafExtCokernelIso_classLaw
#print axioms LinearStudy.affineKoszulOriginalSheafExtCokernelIso_classLaw
#check @LinearStudy.tildeFunctionKoszulComplex_d_next
#print axioms LinearStudy.tildeFunctionKoszulComplex_d_next
#check @LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso
#print axioms LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso
#check @LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso_projection
#print axioms LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso_projection
#check @LinearStudy.affineKoszulOriginalSheafExtGeometricIso
#print axioms LinearStudy.affineKoszulOriginalSheafExtGeometricIso
#check @LinearStudy.affineKoszulOriginalSheafExtGeometricIso_classLaw
#print axioms LinearStudy.affineKoszulOriginalSheafExtGeometricIso_classLaw
#print LinearStudy.tildeOriginalBasisFreeFrame
#print LinearStudy.tildeKoszulActualCutCokernelIso
#print LinearStudy.affineKoszulActualSheafExtTopHomologyIso
#print LinearStudy.affineKoszulActualSheafExtTopModuleExtIso
#print LinearStudy.schemeModuleOriginalTopExtClassIsoLaw
#print LinearStudy.affineKoszulOriginalSheafExtCokernelIso
#print LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso
#print LinearStudy.affineKoszulOriginalSheafExtGeometricIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeOriginalBasisFreeFrame,false),(`LinearStudy.tildeFunctionKoszul_sourceInternalExtAcyclic,true),(`LinearStudy.tildeFunctionKoszul_isZero_above_rank,true),(`LinearStudy.tildeKoszulActualCutCokernelIso,false),(`LinearStudy.tildeKoszulActualCutCokernelIso_projection,true),(`LinearStudy.tildeKoszulActualCutCokernelAugmentation_eq_cofork,true),(`LinearStudy.tildeKoszulActualCutCokernelAugmentation_quasiIso,true),(`LinearStudy.affineKoszulActualSheafExtTopHomologyIso,false),(`LinearStudy.affineKoszulActualSheafExtTopModuleExtIso,false),(`LinearStudy.schemeModuleOriginalTopExtClassIsoLaw,false),(`LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_wholeCokernel,true),(`LinearStudy.schemeModuleOriginalTopExtClassIsoLaw_postcompose,true),(`LinearStudy.affineKoszulOriginalSheafExtCokernelIso,false),(`LinearStudy.affineKoszulOriginalSheafExtCokernelIso_classLaw,true),(`LinearStudy.tildeFunctionKoszulComplex_d_next,true),(`LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso,false),(`LinearStudy.affineKoszulOriginalTopHomCokernelGeometricIso_projection,true),(`LinearStudy.affineKoszulOriginalSheafExtGeometricIso,false),(`LinearStudy.affineKoszulOriginalSheafExtGeometricIso_classLaw,true)]
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
