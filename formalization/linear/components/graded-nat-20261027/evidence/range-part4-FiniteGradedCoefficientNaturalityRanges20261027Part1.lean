module
import all Linear.NativeGeneralNormalizationActualHCoefficient
import all Linear.NativeGeneralNormalizationActualHFactorization
import all Linear.NativeGeneralNormalizationCachedCechComparison
import all Linear.NativeGeneralNormalizationModuleHCoefficient
import all Linear.NativeGeneralNormalizationModuleHFactorization
import all Linear.NativeGeneralSourceAmbientCechBijectionInputs
import all Linear.NativeGeneralSourceAmbientCechHomologyCoefficient
import all Linear.NativeGeneralSourceAmbientCechProductCoefficient
import all Linear.NativeGeneralSourceAmbientCechProductCoefficientTyped
import all Linear.NativeGeneralSourceAmbientCechProductFamilyCoefficient
import all Linear.NativeGeneralSourceAmbientCoefficientBuilder
import all Linear.NativeGeneralSourceAmbientCoefficientSections
import all Linear.NativeGeneralSourceAmbientCoefficientTyped
import all Linear.NativeGeneralSourceAmbientOrderedCechCoefficient
import all Linear.NativeGeneralSourceAmbientOrderedCechCoefficientBuilder
import all Linear.NativeGeneralSourceAmbientOrderedCechCoefficientTargetBuilder
import all Linear.NativeGeneralSourceAmbientOrderedCechCoefficientTyped
import all Linear.NativeGeneralSourceAmbientOrderedTwistCechCoefficient
import all Linear.NativeGeneralSourceAmbientOrderedTwistCechCoefficientBuilder
import all Linear.NativeGeneralSourceAmbientShiftedZeroCechCoefficient
import all Linear.NativeGeneralSourceAmbientShiftedZeroCechComparison
import all Linear.NativeGeneralSourceAmbientTwistComparisonFactorization
import all Linear.NativeProjectiveActualCoefficientBuilder
import all Linear.NativeProjectiveActualCoefficientSquare
import all Linear.NativeProjectiveActualCoefficientTargetBuilder
import all Linear.NativeProjectiveCechCoefficientObjects
import all Linear.NativeProjectiveModuleCechHomologyObjects
import all Linear.OrderedCrossSpaceProductChartCoefficient
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeGeneralNormalizationActualHCoefficient","Linear.NativeGeneralNormalizationActualHFactorization","Linear.NativeGeneralNormalizationCachedCechComparison","Linear.NativeGeneralNormalizationModuleHCoefficient","Linear.NativeGeneralNormalizationModuleHFactorization","Linear.NativeGeneralSourceAmbientCechBijectionInputs","Linear.NativeGeneralSourceAmbientCechHomologyCoefficient","Linear.NativeGeneralSourceAmbientCechProductCoefficient","Linear.NativeGeneralSourceAmbientCechProductCoefficientTyped","Linear.NativeGeneralSourceAmbientCechProductFamilyCoefficient","Linear.NativeGeneralSourceAmbientCoefficientBuilder","Linear.NativeGeneralSourceAmbientCoefficientSections","Linear.NativeGeneralSourceAmbientCoefficientTyped","Linear.NativeGeneralSourceAmbientOrderedCechCoefficient","Linear.NativeGeneralSourceAmbientOrderedCechCoefficientBuilder","Linear.NativeGeneralSourceAmbientOrderedCechCoefficientTargetBuilder","Linear.NativeGeneralSourceAmbientOrderedCechCoefficientTyped","Linear.NativeGeneralSourceAmbientOrderedTwistCechCoefficient","Linear.NativeGeneralSourceAmbientOrderedTwistCechCoefficientBuilder","Linear.NativeGeneralSourceAmbientShiftedZeroCechCoefficient","Linear.NativeGeneralSourceAmbientShiftedZeroCechComparison","Linear.NativeGeneralSourceAmbientTwistComparisonFactorization","Linear.NativeProjectiveActualCoefficientBuilder","Linear.NativeProjectiveActualCoefficientSquare","Linear.NativeProjectiveActualCoefficientTargetBuilder","Linear.NativeProjectiveCechCoefficientObjects","Linear.NativeProjectiveModuleCechHomologyObjects","Linear.OrderedCrossSpaceProductChartCoefficient"]
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
