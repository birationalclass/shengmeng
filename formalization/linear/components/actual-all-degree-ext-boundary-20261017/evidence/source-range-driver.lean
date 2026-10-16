module
import all Linear.CochainConeLiftClassAllDegrees
import all Linear.CochainConeLiftClassBridge
import all Linear.CochainConeLiftDerivedAllDegrees
import all Linear.CochainConeLiftDerivedBridge
import all Linear.CochainConeLiftTriangleDegrees
import all Linear.HomCocycleShiftedComposition
import all Linear.ShortExactInjectiveCochainLift
import all Linear.ShortExactInjectiveCochainLiftAllDegrees
import all Linear.ShortExactInjectiveCocycleAllDegrees
import all Linear.ShortExactInjectiveExtBoundaryAllDegrees
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
  if count != 14 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
