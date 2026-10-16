module
import all Linear.CochainAugmentationOpcycle
import all Linear.CochainAugmentedTopHomotopyComponents
import all Linear.CochainCocycleOfHomShifted
import all Linear.CochainOpcycleInjectiveBoundaryComponents
import all Linear.CochainOpcycleIteratedBoundary
import all Linear.CochainOpcycleSourceSequence
import all Linear.CochainResolutionIteratedSourceBoundary
import all Linear.CochainResolutionSourceBoundaryClass
import all Linear.CochainResolutionSourceBoundaryFamily
import all Linear.CochainResolutionSourceLiftEquations
import all Linear.CochainResolutionTopHomotopyEquations
import all Linear.CochainSingleSupportComponents
import all Linear.CochainSourceLiftClasses
import all Linear.CochainSourceLiftComponentRecurrence
import all Linear.CochainSourceLiftFamily
import all Linear.CochainSourceLiftInitialClass
import all Linear.CochainSourceLiftRecurrence
import all Linear.CochainSourceLiftSigns
import all Linear.CochainSourceLiftTerminalClass
import all Linear.InjectiveCochainCocycleSourceClass
import all Linear.InjectiveCochainDegreeZeroClass
import all Linear.OriginalChainIteratedSourceBoundary
import all Linear.OriginalChainStandardSourceBoundaryStatement
import all Linear.ProjectivePulledOriginalSetupSourceBoundaryFamily
import all Linear.ProjectivePulledOriginalWholeCutSourceBoundaryStatement
import all Linear.ShortExactInjectiveBoundaryComponents
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.CochainAugmentationOpcycle,`Linear.CochainAugmentedTopHomotopyComponents,`Linear.CochainCocycleOfHomShifted,`Linear.CochainOpcycleInjectiveBoundaryComponents,`Linear.CochainOpcycleIteratedBoundary,`Linear.CochainOpcycleSourceSequence,`Linear.CochainResolutionIteratedSourceBoundary,`Linear.CochainResolutionSourceBoundaryClass,`Linear.CochainResolutionSourceBoundaryFamily,`Linear.CochainResolutionSourceLiftEquations,`Linear.CochainResolutionTopHomotopyEquations,`Linear.CochainSingleSupportComponents,`Linear.CochainSourceLiftClasses,`Linear.CochainSourceLiftComponentRecurrence,`Linear.CochainSourceLiftFamily,`Linear.CochainSourceLiftInitialClass,`Linear.CochainSourceLiftRecurrence,`Linear.CochainSourceLiftSigns,`Linear.CochainSourceLiftTerminalClass,`Linear.InjectiveCochainCocycleSourceClass,`Linear.InjectiveCochainDegreeZeroClass,`Linear.OriginalChainIteratedSourceBoundary,`Linear.OriginalChainStandardSourceBoundaryStatement,`Linear.ProjectivePulledOriginalSetupSourceBoundaryFamily,`Linear.ProjectivePulledOriginalWholeCutSourceBoundaryStatement,`Linear.ShortExactInjectiveBoundaryComponents] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 54 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
