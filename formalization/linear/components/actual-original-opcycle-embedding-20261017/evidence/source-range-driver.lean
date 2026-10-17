module
import all Linear.OriginalChainOpcycleEmbedding
import all Linear.OriginalChainTerminalSourceIso
import all Linear.OriginalChainTopOpcycleEmbedding
import all Linear.SchemeModuleGlobalToInternalExtSourceIso
import all Linear.SchemeModuleHomShortComplexSourceMap
import all Linear.SchemeModuleHomZeroBoundaryCokernel
import all Linear.SchemeModuleHomZeroSourceNaturality
import all Linear.SchemeModuleInternalExtBoundarySourceNaturality
import all Linear.SchemeModuleOriginalBoundaryEmbedding
import all Linear.SchemeModuleOriginalFirstBoundaryCokernel
import all Linear.SchemeModuleOriginalOpcycleSourceIso
import all Linear.SchemeModuleOriginalSmallClassInternalImage
import all Linear.SchemeModuleOriginalTopInitialClassEmbedding
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.OriginalChainOpcycleEmbedding,`Linear.OriginalChainTerminalSourceIso,`Linear.OriginalChainTopOpcycleEmbedding,`Linear.SchemeModuleGlobalToInternalExtSourceIso,`Linear.SchemeModuleHomShortComplexSourceMap,`Linear.SchemeModuleHomZeroBoundaryCokernel,`Linear.SchemeModuleHomZeroSourceNaturality,`Linear.SchemeModuleInternalExtBoundarySourceNaturality,`Linear.SchemeModuleOriginalBoundaryEmbedding,`Linear.SchemeModuleOriginalFirstBoundaryCokernel,`Linear.SchemeModuleOriginalOpcycleSourceIso,`Linear.SchemeModuleOriginalSmallClassInternalImage,`Linear.SchemeModuleOriginalTopInitialClassEmbedding] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 20 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
