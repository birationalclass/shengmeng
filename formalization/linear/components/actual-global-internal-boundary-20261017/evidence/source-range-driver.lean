module
import all Linear.InjectiveNativeDegreeZeroClass
import all Linear.OriginalChainTopExtUniverse
import all Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary
import all Linear.SchemeModuleCochainInternalBoundaryStep
import all Linear.SchemeModuleCochainIteratedInternalBoundary
import all Linear.SchemeModuleCochainResolutionInternalBoundaryClass
import all Linear.SchemeModuleGlobalToInternalExtAllDegrees
import all Linear.SchemeModuleGlobalToInternalExtBoundary
import all Linear.SchemeModuleGlobalToInternalExtIteration
import all Linear.SchemeModuleGlobalToInternalExtZeroBoundary
import all Linear.SchemeModuleHomToInternalExtZero
import all Linear.SchemeModuleHomZeroInjectiveClass
import all Linear.SchemeModuleHomZeroInjectiveCycle
import all Linear.SchemeModuleInjectiveCocycleBoundary
import all Linear.SchemeModuleInjectiveCocycleEvaluation
import all Linear.SchemeModuleInjectiveInternalHomBoundaryClass
import all Linear.SchemeModuleOriginalChainInternalBoundaryClass
import all Linear.SchemeModuleOriginalSmallClassBoundary
import all Linear.ShortExactInjectiveNativeBoundaryComponents
import all Linear.ShortExactInjectiveNativeLifts
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.InjectiveNativeDegreeZeroClass,`Linear.OriginalChainTopExtUniverse,`Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary,`Linear.SchemeModuleCochainInternalBoundaryStep,`Linear.SchemeModuleCochainIteratedInternalBoundary,`Linear.SchemeModuleCochainResolutionInternalBoundaryClass,`Linear.SchemeModuleGlobalToInternalExtAllDegrees,`Linear.SchemeModuleGlobalToInternalExtBoundary,`Linear.SchemeModuleGlobalToInternalExtIteration,`Linear.SchemeModuleGlobalToInternalExtZeroBoundary,`Linear.SchemeModuleHomToInternalExtZero,`Linear.SchemeModuleHomZeroInjectiveClass,`Linear.SchemeModuleHomZeroInjectiveCycle,`Linear.SchemeModuleInjectiveCocycleBoundary,`Linear.SchemeModuleInjectiveCocycleEvaluation,`Linear.SchemeModuleInjectiveInternalHomBoundaryClass,`Linear.SchemeModuleOriginalChainInternalBoundaryClass,`Linear.SchemeModuleOriginalSmallClassBoundary,`Linear.ShortExactInjectiveNativeBoundaryComponents,`Linear.ShortExactInjectiveNativeLifts] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 28 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
