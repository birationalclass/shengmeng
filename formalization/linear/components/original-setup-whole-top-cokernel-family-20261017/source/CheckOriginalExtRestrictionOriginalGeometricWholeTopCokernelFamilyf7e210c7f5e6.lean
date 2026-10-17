module
import all Linear.SchemeModuleOriginalWholeTopCokernelStatement
import all Linear.ProjectivePulledOriginalWholeTopCokernelStatement
import all Linear.ProjectivePulledOriginalSetupWholeTopCokernelFamily
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalWholeTopCokernelStatement
#print axioms LinearStudy.schemeModuleOriginalWholeTopCokernelStatement
#check @LinearStudy.schemeModuleOriginalWholeTopCokernelStatement_proof
#print axioms LinearStudy.schemeModuleOriginalWholeTopCokernelStatement_proof
#check @LinearStudy.projectivePulledOriginalWholeTopCokernelStatement
#print axioms LinearStudy.projectivePulledOriginalWholeTopCokernelStatement
#check @LinearStudy.projectivePulledOriginalWholeTopCokernelStatement_proof
#print axioms LinearStudy.projectivePulledOriginalWholeTopCokernelStatement_proof
#check @LinearStudy.projectivePulledOriginalSetupWholeTopCokernelFamilyProof
#print axioms LinearStudy.projectivePulledOriginalSetupWholeTopCokernelFamilyProof
#print LinearStudy.schemeModuleOriginalWholeTopCokernelStatement
#print LinearStudy.projectivePulledOriginalWholeTopCokernelStatement
#print LinearStudy.projectivePulledOriginalSetupWholeTopCokernelFamilyProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalWholeTopCokernelStatement,false),(`LinearStudy.schemeModuleOriginalWholeTopCokernelStatement_proof,true),(`LinearStudy.projectivePulledOriginalWholeTopCokernelStatement,false),(`LinearStudy.projectivePulledOriginalWholeTopCokernelStatement_proof,true),(`LinearStudy.projectivePulledOriginalSetupWholeTopCokernelFamilyProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
