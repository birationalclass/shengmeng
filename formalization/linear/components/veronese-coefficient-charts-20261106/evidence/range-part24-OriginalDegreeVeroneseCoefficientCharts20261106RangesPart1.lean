module
import all Linear.NativeGradedWeightedChartImage
import all Linear.OriginalDegreeVeroneseCoefficient
import all Linear.OriginalDegreeVeroneseCoefficientAmbientRestriction
import all Linear.OriginalDegreeVeroneseCoefficientChartDegree
import all Linear.OriginalDegreeVeroneseCoefficientChartEquiv
import all Linear.OriginalDegreeVeroneseCoefficientChartFraction
import all Linear.OriginalDegreeVeroneseCoefficientChartImage
import all Linear.OriginalDegreeVeroneseCoefficientChartScalar
import all Linear.OriginalDegreeVeroneseCoefficientFractionValues
import all Linear.OriginalDegreeVeroneseCoefficientGrading
import all Linear.OriginalDegreeVeroneseCoefficientLocalization
import all Linear.OriginalDegreeVeroneseCoefficientLocalizationAction
import all Linear.OriginalDegreeVeroneseCoefficientLocalizationAdd
import all Linear.OriginalDegreeVeroneseCoefficientLocalizationOverlap
import all Linear.OriginalDegreeVeroneseCoefficientRegradedChart
import all Linear.OriginalDegreeVeroneseCoefficientRestrictionSquare
import all Linear.OriginalDegreeVeroneseCoefficientScalarValue
import all Linear.OriginalDegreeVeroneseCoefficientWeightedRestriction
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeGradedWeightedChartImage","Linear.OriginalDegreeVeroneseCoefficient","Linear.OriginalDegreeVeroneseCoefficientAmbientRestriction","Linear.OriginalDegreeVeroneseCoefficientChartDegree","Linear.OriginalDegreeVeroneseCoefficientChartEquiv","Linear.OriginalDegreeVeroneseCoefficientChartFraction","Linear.OriginalDegreeVeroneseCoefficientChartImage","Linear.OriginalDegreeVeroneseCoefficientChartScalar","Linear.OriginalDegreeVeroneseCoefficientFractionValues","Linear.OriginalDegreeVeroneseCoefficientGrading","Linear.OriginalDegreeVeroneseCoefficientLocalization","Linear.OriginalDegreeVeroneseCoefficientLocalizationAction","Linear.OriginalDegreeVeroneseCoefficientLocalizationAdd","Linear.OriginalDegreeVeroneseCoefficientLocalizationOverlap","Linear.OriginalDegreeVeroneseCoefficientRegradedChart","Linear.OriginalDegreeVeroneseCoefficientRestrictionSquare","Linear.OriginalDegreeVeroneseCoefficientScalarValue","Linear.OriginalDegreeVeroneseCoefficientWeightedRestriction"]
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
