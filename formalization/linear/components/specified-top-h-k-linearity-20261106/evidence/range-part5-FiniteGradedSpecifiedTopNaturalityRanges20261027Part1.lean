module
import all Linear.CoordinateCechCoefficientForgettingIdentity
import all Linear.CoordinateNativeCechAbelianModel
import all Linear.CoordinateNativeCechAbelianModelCoefficient
import all Linear.CoordinateNativeCechHomologyModel
import all Linear.IntegerFinitePresentationAbelianCoefficientNaturality
import all Linear.IntegerFinitePresentationAbelianComparisonCoefficientProof
import all Linear.IntegerFinitePresentationAbelianComparisonFactorization
import all Linear.IntegerFinitePresentationAbelianComparisonObject
import all Linear.IntegerFinitePresentationCoordinateNaturality
import all Linear.IntegerGradedHomDualCoefficientObjects
import all Linear.NativeGeneralPolynomialNormalizationModuleHCoefficient
import all Linear.NativeGeneralSpecifiedNormalizationAbelianFactorization
import all Linear.NativeGeneralSpecifiedNormalizationCoefficientData
import all Linear.NativeGeneralSpecifiedNormalizationCoefficientDataIdentity
import all Linear.NativeGeneralSpecifiedNormalizationFactorization
import all Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficient
import all Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficientTyped
import all Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficientVariables
import all Linear.SpecifiedDualityCoefficientTransfer
import all Linear.SpecifiedDualityFactorizationData
import all Linear.SpecifiedDualitySourceCoefficientBuilder
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.CoordinateCechCoefficientForgettingIdentity","Linear.CoordinateNativeCechAbelianModel","Linear.CoordinateNativeCechAbelianModelCoefficient","Linear.CoordinateNativeCechHomologyModel","Linear.IntegerFinitePresentationAbelianCoefficientNaturality","Linear.IntegerFinitePresentationAbelianComparisonCoefficientProof","Linear.IntegerFinitePresentationAbelianComparisonFactorization","Linear.IntegerFinitePresentationAbelianComparisonObject","Linear.IntegerFinitePresentationCoordinateNaturality","Linear.IntegerGradedHomDualCoefficientObjects","Linear.NativeGeneralPolynomialNormalizationModuleHCoefficient","Linear.NativeGeneralSpecifiedNormalizationAbelianFactorization","Linear.NativeGeneralSpecifiedNormalizationCoefficientData","Linear.NativeGeneralSpecifiedNormalizationCoefficientDataIdentity","Linear.NativeGeneralSpecifiedNormalizationFactorization","Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficient","Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficientTyped","Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficientVariables","Linear.SpecifiedDualityCoefficientTransfer","Linear.SpecifiedDualityFactorizationData","Linear.SpecifiedDualitySourceCoefficientBuilder"]
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
