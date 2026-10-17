module
import all Linear.OriginalChainOpcycleIndex
import all Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit
import all Linear.SchemeModuleOriginalBoundarySequenceComparison
import all Linear.SchemeModuleOriginalBoundaryStepNaturality
import all Linear.SchemeModuleOriginalNatBoundaryStep
import all Linear.SchemeModuleOriginalNatClassImage
import all Linear.SchemeModuleOriginalNatTargetExt
import all Linear.SchemeModuleOriginalOpcycleExtComparison
import all Linear.SchemeModuleOriginalOpcycleExtIndex
import all Linear.SchemeModuleOriginalPositiveBoundaryIso
import all Linear.SchemeModuleOriginalWholeTopCokernel
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.OriginalChainOpcycleIndex,`Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit,`Linear.SchemeModuleOriginalBoundarySequenceComparison,`Linear.SchemeModuleOriginalBoundaryStepNaturality,`Linear.SchemeModuleOriginalNatBoundaryStep,`Linear.SchemeModuleOriginalNatClassImage,`Linear.SchemeModuleOriginalNatTargetExt,`Linear.SchemeModuleOriginalOpcycleExtComparison,`Linear.SchemeModuleOriginalOpcycleExtIndex,`Linear.SchemeModuleOriginalPositiveBoundaryIso,`Linear.SchemeModuleOriginalWholeTopCokernel] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 24 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
