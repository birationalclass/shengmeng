module
import all Linear.NativeGeneralSourceAmbientCechHomologyScalar
import all Linear.NativeGeneralSourceAmbientCechProductScalar
import all Linear.NativeGeneralSourceAmbientCechProductScalarProof
import all Linear.NativeGeneralSourceAmbientCechSectionScalarProof
import all Linear.NativeGeneralSourceAmbientOrderedCechScalar
import all Linear.NativeGeneralSourceAmbientOrderedCechScalarProof
import all Linear.NativeGeneralSourceAmbientOrderedTwistCechScalar
import all Linear.NativeGeneralSourceAmbientOrderedTwistScalarIsoProof
import all Linear.NativeGeneralSourceAmbientOriginalBaseScalar
import all Linear.NativeGeneralSourceAmbientOriginalBaseScalarTyped
import all Linear.NativeGeneralSourceAmbientShiftedZeroCechScalarSquare
import all Linear.NativeOrderedCechRegradingScalarSquares
import all Linear.NativeProjectiveModuleBaseScalarValue
import all Linear.NativeProjectiveModuleScalarApply
import all Linear.NativeProjectiveOrderedBaseScalarMap
import all Linear.NativeProjectiveOriginalBaseScalarMap
import all Linear.NativeProjectiveOriginalScalarPointwise
import all Linear.NativeProjectiveOriginalScalarPointwiseActual
import all Linear.NativeProjectiveOriginalScalarPointwiseBothActual
import all Linear.NativeProjectiveOriginalScalarSourceBuilder
import all Linear.NativeProjectiveOriginalScalarSquare
import all Linear.NativeProjectiveOriginalScalarTargetBuilder
import all Linear.NativeWeightedSourceAmbientOriginalBaseScalar
import all Linear.NativeWeightedSourceAmbientSectionScalar
import all Linear.NormalizationChartConstants
import all Linear.OrderedCechIsoOriginalScalar
import all Linear.OriginalScalarComparisonCalibration
import all Linear.OriginalThreeIsoScalarSquare
import all Linear.ProjBasicOpenBaseScalar
import all Linear.ProjBasicOpenNormalizationBaseScalar
import all Linear.ProjStructureSectionRestriction
import all Linear.ProjStructureSectionScalarValue
import all Linear.SchemeModuleActualAbelianScalarValue
import all Linear.SemilinearComparisonScalar
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeGeneralSourceAmbientCechHomologyScalar","Linear.NativeGeneralSourceAmbientCechProductScalar","Linear.NativeGeneralSourceAmbientCechProductScalarProof","Linear.NativeGeneralSourceAmbientCechSectionScalarProof","Linear.NativeGeneralSourceAmbientOrderedCechScalar","Linear.NativeGeneralSourceAmbientOrderedCechScalarProof","Linear.NativeGeneralSourceAmbientOrderedTwistCechScalar","Linear.NativeGeneralSourceAmbientOrderedTwistScalarIsoProof","Linear.NativeGeneralSourceAmbientOriginalBaseScalar","Linear.NativeGeneralSourceAmbientOriginalBaseScalarTyped","Linear.NativeGeneralSourceAmbientShiftedZeroCechScalarSquare","Linear.NativeOrderedCechRegradingScalarSquares","Linear.NativeProjectiveModuleBaseScalarValue","Linear.NativeProjectiveModuleScalarApply","Linear.NativeProjectiveOrderedBaseScalarMap","Linear.NativeProjectiveOriginalBaseScalarMap","Linear.NativeProjectiveOriginalScalarPointwise","Linear.NativeProjectiveOriginalScalarPointwiseActual","Linear.NativeProjectiveOriginalScalarPointwiseBothActual","Linear.NativeProjectiveOriginalScalarSourceBuilder","Linear.NativeProjectiveOriginalScalarSquare","Linear.NativeProjectiveOriginalScalarTargetBuilder","Linear.NativeWeightedSourceAmbientOriginalBaseScalar","Linear.NativeWeightedSourceAmbientSectionScalar","Linear.NormalizationChartConstants","Linear.OrderedCechIsoOriginalScalar","Linear.OriginalScalarComparisonCalibration","Linear.OriginalThreeIsoScalarSquare","Linear.ProjBasicOpenBaseScalar","Linear.ProjBasicOpenNormalizationBaseScalar","Linear.ProjStructureSectionRestriction","Linear.ProjStructureSectionScalarValue","Linear.SchemeModuleActualAbelianScalarValue","Linear.SemilinearComparisonScalar"]
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
