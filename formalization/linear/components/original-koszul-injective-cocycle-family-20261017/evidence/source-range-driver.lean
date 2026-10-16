module
import all Linear.CochainClassEqBoundary
import all Linear.CochainKInjectiveDerivedCocycle
import all Linear.CochainResolutionInjectiveCocycle
import all Linear.OriginalChainCokernelTopInjectiveCocycle
import all Linear.OriginalChainOrderedTopCocycle
import all Linear.OriginalChainStandardTopInjectiveCocycle
import all Linear.OriginalChainStandardTopInjectiveStatement
import all Linear.OriginalChainTopInjectiveCocycle
import all Linear.ProjectivePulledOriginalSetupInjectiveCocycleFamily
import all Linear.ProjectivePulledOriginalWholeCutInjectiveCocycle
import all Linear.ProjectivePulledOriginalWholeCutInjectiveStatement
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.CochainClassEqBoundary,`Linear.CochainKInjectiveDerivedCocycle,`Linear.CochainResolutionInjectiveCocycle,`Linear.OriginalChainCokernelTopInjectiveCocycle,`Linear.OriginalChainOrderedTopCocycle,`Linear.OriginalChainStandardTopInjectiveCocycle,`Linear.OriginalChainStandardTopInjectiveStatement,`Linear.OriginalChainTopInjectiveCocycle,`Linear.ProjectivePulledOriginalSetupInjectiveCocycleFamily,`Linear.ProjectivePulledOriginalWholeCutInjectiveCocycle,`Linear.ProjectivePulledOriginalWholeCutInjectiveStatement] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 15 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
