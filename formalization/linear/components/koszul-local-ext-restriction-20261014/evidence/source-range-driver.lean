module
import all Linear.ExtendScalarsActualTensor
import all Linear.KoszulExactResolution
import all Linear.KoszulFunctionResolution
import all Linear.KoszulHomotopyTop
import all Linear.KoszulLocalGlobalExact
import all Linear.KoszulResolution
import all Linear.KoszulTop
import all Linear.KoszulTopComplementFunctional
import all Linear.KoszulTopDualCokernelRestriction
import all Linear.KoszulTopExtRepresentatives
import all Linear.KoszulTopExtRestrictionEquiv
import all Linear.LocalComplexExactReflection
import all Linear.LocalExactReflection
import all Linear.TildeBasicOpenMono
import all Linear.TildeComplexExact
import all Linear.TildeKoszulDualTopRestriction
import all Linear.TildeKoszulPresentation
import all Linear.TildeKoszulStructureAugmentation
import all Linear.TildePreservesMono
import all Linear.TildePushforward
import all Linear.TildeQuotientPushforward
import all Linear.Vendor.ExteriorBaseChange
import all Linear.Vendor.ExteriorProduct
import all Linear.Vendor.KoszulComplex
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
  if count <= 27 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
