module
import all Linear.OriginalChainOpcycleIndex
import all Linear.SchemeModuleOriginalOpcycleExtIndex
import all Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit
import all Linear.SchemeModuleOriginalNatBoundaryStep
import all Linear.SchemeModuleOriginalOpcycleExtComparison
import all Linear.SchemeModuleOriginalBoundaryStepNaturality
import all Linear.SchemeModuleOriginalBoundarySequenceComparison
import all Linear.SchemeModuleOriginalNatClassImage
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalChainAsCochainOpcyclesIso_index
#print axioms LinearStudy.originalChainAsCochainOpcyclesIso_index
#check @LinearStudy.schemeModuleOriginalOpcycleExtSourceMap_index
#print axioms LinearStudy.schemeModuleOriginalOpcycleExtSourceMap_index
#check @LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding_explicit
#print axioms LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding_explicit
#check @LinearStudy.schemeModuleOriginalNatBoundaryStep
#print axioms LinearStudy.schemeModuleOriginalNatBoundaryStep
#check @LinearStudy.schemeModuleOriginalNatBoundaryStep_eq
#print axioms LinearStudy.schemeModuleOriginalNatBoundaryStep_eq
#check @LinearStudy.schemeModuleOriginalNatBoundaryStep_eq_zero
#print axioms LinearStudy.schemeModuleOriginalNatBoundaryStep_eq_zero
#check @LinearStudy.schemeModuleOriginalOpcycleExtComparison
#print axioms LinearStudy.schemeModuleOriginalOpcycleExtComparison
#check @LinearStudy.schemeModuleOriginalOpcycleExtComparison_eq
#print axioms LinearStudy.schemeModuleOriginalOpcycleExtComparison_eq
#check @LinearStudy.schemeModuleOriginalBoundaryStep_naturality
#print axioms LinearStudy.schemeModuleOriginalBoundaryStep_naturality
#check @LinearStudy.schemeModuleOriginalBoundarySequenceComparison
#print axioms LinearStudy.schemeModuleOriginalBoundarySequenceComparison
#check @LinearStudy.schemeModuleOriginalNatIteratedBoundary
#print axioms LinearStudy.schemeModuleOriginalNatIteratedBoundary
#check @LinearStudy.schemeModuleOriginalBoundaryIteration_naturality
#print axioms LinearStudy.schemeModuleOriginalBoundaryIteration_naturality
#check @LinearStudy.schemeModuleOriginalInitialClass_comparison
#print axioms LinearStudy.schemeModuleOriginalInitialClass_comparison
#check @LinearStudy.schemeModuleOriginalSmallClass_nativeIterationImage
#print axioms LinearStudy.schemeModuleOriginalSmallClass_nativeIterationImage
#print LinearStudy.schemeModuleOriginalNatBoundaryStep
#print LinearStudy.schemeModuleOriginalOpcycleExtComparison
#print LinearStudy.schemeModuleOriginalBoundarySequenceComparison
#print LinearStudy.schemeModuleOriginalNatIteratedBoundary
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalChainAsCochainOpcyclesIso_index,true),(`LinearStudy.schemeModuleOriginalOpcycleExtSourceMap_index,true),(`LinearStudy.schemeModuleOriginalOpcycleBoundary_embedding_explicit,true),(`LinearStudy.schemeModuleOriginalNatBoundaryStep,false),(`LinearStudy.schemeModuleOriginalNatBoundaryStep_eq,true),(`LinearStudy.schemeModuleOriginalNatBoundaryStep_eq_zero,true),(`LinearStudy.schemeModuleOriginalOpcycleExtComparison,false),(`LinearStudy.schemeModuleOriginalOpcycleExtComparison_eq,true),(`LinearStudy.schemeModuleOriginalBoundaryStep_naturality,true),(`LinearStudy.schemeModuleOriginalBoundarySequenceComparison,false),(`LinearStudy.schemeModuleOriginalNatIteratedBoundary,false),(`LinearStudy.schemeModuleOriginalBoundaryIteration_naturality,true),(`LinearStudy.schemeModuleOriginalInitialClass_comparison,true),(`LinearStudy.schemeModuleOriginalSmallClass_nativeIterationImage,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
