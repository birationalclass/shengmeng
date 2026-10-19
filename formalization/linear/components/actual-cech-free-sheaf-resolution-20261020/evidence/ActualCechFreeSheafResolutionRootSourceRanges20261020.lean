module
import all Linear.AugmentedAlternatingWhiskering
import all Linear.AugmentedPointwiseWhiskering
import all Linear.CoverGeneratedTerminalPresheaf
import all Linear.FormalCechFormalEvaluation
import all Linear.FormalCechPresheafResolution
import all Linear.FormalCechSimplicialResolution
import all Linear.FormalCechYonedaAdjunction
import all Linear.FormalCoproductFunctorMap
import all Linear.TopCechFreeSheafResolution
import all Linear.TopCechIntegerTarget
import all Linear.TopCoverGeneratedTerminalSheaf
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AugmentedAlternatingWhiskering,`Linear.AugmentedPointwiseWhiskering,`Linear.CoverGeneratedTerminalPresheaf,`Linear.FormalCechFormalEvaluation,`Linear.FormalCechPresheafResolution,`Linear.FormalCechSimplicialResolution,`Linear.FormalCechYonedaAdjunction,`Linear.FormalCoproductFunctorMap,`Linear.TopCechFreeSheafResolution,`Linear.TopCechIntegerTarget,`Linear.TopCoverGeneratedTerminalSheaf] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 32 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
