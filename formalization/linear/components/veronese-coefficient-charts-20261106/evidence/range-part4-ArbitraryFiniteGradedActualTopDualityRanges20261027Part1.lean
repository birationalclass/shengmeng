module
import all Linear.NativeCechProductChartFaces
import all Linear.NativeGeneralActualHCompatibility
import all Linear.NativeGeneralNormalizationActualHComparison
import all Linear.NativeGeneralNormalizationHCompatibility
import all Linear.NativeGeneralNormalizationModuleHComparison
import all Linear.NativeGeneralSourceAmbientCechFaces
import all Linear.NativeGeneralSourceAmbientCechObjects
import all Linear.NativeGeneralSourceAmbientCechProductFamily
import all Linear.NativeGeneralSourceAmbientComparisonCompatibility
import all Linear.NativeGeneralSourceAmbientOrderedCech
import all Linear.NativeGeneralSourceAmbientOrderedCechBuilder
import all Linear.NativeGeneralSourceAmbientOrderedTwistCech
import all Linear.NativeGeneralSpecifiedNormalizationTopDuality
import all Linear.OrderedAbelianOpenSectionTransport
import all Linear.OrderedCechDeleteValue
import all Linear.OrderedCrossSpaceProductChartComplexIso
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeCechProductChartFaces","Linear.NativeGeneralActualHCompatibility","Linear.NativeGeneralNormalizationActualHComparison","Linear.NativeGeneralNormalizationHCompatibility","Linear.NativeGeneralNormalizationModuleHComparison","Linear.NativeGeneralSourceAmbientCechFaces","Linear.NativeGeneralSourceAmbientCechObjects","Linear.NativeGeneralSourceAmbientCechProductFamily","Linear.NativeGeneralSourceAmbientComparisonCompatibility","Linear.NativeGeneralSourceAmbientOrderedCech","Linear.NativeGeneralSourceAmbientOrderedCechBuilder","Linear.NativeGeneralSourceAmbientOrderedTwistCech","Linear.NativeGeneralSpecifiedNormalizationTopDuality","Linear.OrderedAbelianOpenSectionTransport","Linear.OrderedCechDeleteValue","Linear.OrderedCrossSpaceProductChartComplexIso"]
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  let mut count : Nat := 0
  let mut seen : Lean.NameSet := {}
  for i in [:env.header.moduleData.size] do
    let owner := env.header.moduleNames[i]!
    unless selected.contains owner.toString do continue
    let data := env.header.moduleData[i]!
    for name in data.constNames ++ data.extraConstNames do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | continue
      let some idx := env.getModuleIdxFor? name | continue
      let modName := env.header.moduleNames[idx]!
      unless selected.contains modName.toString do continue
      let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.filter isOwn |>.map toString)
      Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
      let some ranges ← Lean.findDeclarationRanges? name | continue
      let q := ranges.range
      Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{q.pos.line}|{q.pos.column}|{q.endPos.line}|{q.endPos.column}|{deps}"
      count := count+1
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
