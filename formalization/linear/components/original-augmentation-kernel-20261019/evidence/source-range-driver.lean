module
import all Linear.CochainResolutionAugmentationZero
import all Linear.CochainResolutionExtSourceSquare
import all Linear.OriginalChainAugmentationClassZero
import all Linear.ParameterFamilyEnrichPreserveShared
import all Linear.ProjectivePulledOriginalAugmentationZero
import all Linear.ProjectivePulledOriginalSetupAugmentationKernelFamily
import all Linear.SchemeModuleOriginalClassAugmentationZero
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.CochainResolutionAugmentationZero,`Linear.CochainResolutionExtSourceSquare,`Linear.OriginalChainAugmentationClassZero,`Linear.ParameterFamilyEnrichPreserveShared,`Linear.ProjectivePulledOriginalAugmentationZero,`Linear.ProjectivePulledOriginalSetupAugmentationKernelFamily,`Linear.SchemeModuleOriginalClassAugmentationZero] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 15 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
