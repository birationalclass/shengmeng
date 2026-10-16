module
import all Linear.ChainActualCokernelAugmentation
import all Linear.ChainResolutionAsCochain
import all Linear.ChainResolutionTopExtClass
import all Linear.CochainConeLiftClassBridge
import all Linear.CochainConeLiftDerivedBridge
import all Linear.CochainConeLiftTriangleEquation
import all Linear.CochainResolutionExtClass
import all Linear.CochainResolutionExtClassAdditive
import all Linear.CochainResolutionExtClassCongruence
import all Linear.CochainResolutionSourceQuasiIso
import all Linear.CochainResolutionTopExtNaturality
import all Linear.CochainShortExactRoofClass
import all Linear.OriginalChainDegreeOneBoundaryClass
import all Linear.OriginalChainDegreeOneConeAugmentation
import all Linear.OriginalChainDegreeOneConeMap
import all Linear.OriginalChainDegreeOneConeQuasiIso
import all Linear.OriginalChainDegreeOneConeTopCocycle
import all Linear.OriginalChainDegreeOneInjectiveCocycle
import all Linear.OriginalChainDegreeOneRoofClass
import all Linear.ShortExactInjectiveCochainLift
import all Linear.ShortExactInjectiveCocycleRealization
import all Linear.ShortExactRoofInjectiveCocycle
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !modName.toString.startsWith "Linear." && modName != `Linear then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 38 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
