module
import all Linear.HomogeneousQuotientNativeChartFactorNaturality
import all Linear.HomogeneousQuotientNativeCutChartMap
import all Linear.HomogeneousQuotientOriginalCutCover
import all Linear.HomogeneousRatioFieldMap
import all Linear.HomogeneousRationalIdeal
import all Linear.HomogeneousRationalPullback
import all Linear.InjectiveCochainCocycleSourceClass
import all Linear.InjectiveCochainDegreeZeroClass
import all Linear.InjectiveCocycleExtPresentation
import all Linear.InjectiveCocycleSourceNaturality
import all Linear.InjectiveCocycleTransport
import all Linear.InjectiveNativeDegreeZeroClass
import all Linear.IntegerGradedFiniteFreeSurjection
import all Linear.IntegerGradedFinitePresentation
import all Linear.IntegerGradedFiniteRelations
import all Linear.IntegerGradedHomogeneousAnnihilator
import all Linear.IntegerGradedKernelGenerators
import all Linear.IntegerGradedModuleGenerators
import all Linear.IntegerGradedModuleProjection
import all Linear.IntegerGradedRingProduct
import all Linear.IntegerGradedSubmoduleDecomposition
import all Linear.IntegerGradedSurjectionPreimage
import all Linear.IntegerGradingShift
import all Linear.IntegerShiftedFreeDecomposition
import all Linear.IntegerShiftedFreeDualRelations
import all Linear.IntegerShiftedFreeGeneralRelationPi
import all Linear.IntegerShiftedFreeGeneratorMap
import all Linear.IntegerShiftedFreeGradedDualRelation
import all Linear.IntegerShiftedFreeHomCoordinates
import all Linear.IntegerShiftedFreeHomPiCoordinates
import all Linear.IntegerShiftedFreeMatrix
import all Linear.IntegerShiftedFreePieces
import all Linear.IntegerShiftedFreeRegradingPresentation
import all Linear.IntegralKrullDimension
import all Linear.Iteration
import all Linear.JacobianNonzero
import all Linear.JacobianSpecialization
import all Linear.JacobianTrace
import all Linear.KoszulComparison
import all Linear.KoszulCoordinateEntryNaturality
import all Linear.KoszulCoordinateWholeNaturality
import all Linear.KoszulExactResolution
import all Linear.KoszulFunctionResolution
import all Linear.KoszulFunctionUnit
import all Linear.KoszulFunctionUnitAllDegrees
import all Linear.KoszulHomogeneousCoordinates
import all Linear.KoszulHomotopyTop
import all Linear.KoszulLocalGlobalExact
import all Linear.KoszulResolution
import all Linear.KoszulRingEquivExact
import all Linear.KoszulSocleDeterminant
import all Linear.KoszulSocleMap
import all Linear.KoszulTop
import all Linear.KoszulTopComplementFunctional
import all Linear.KoszulTopHomCoefficientRestriction
import all Linear.KoszulUnitExactness
import all Linear.LiftedParameterCoordinates
import all Linear.LiftedParameterMaps
import all Linear.LiftedParameterPresentation
import all Linear.LiftedParametersRegular
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.HomogeneousQuotientNativeChartFactorNaturality","Linear.HomogeneousQuotientNativeCutChartMap","Linear.HomogeneousQuotientOriginalCutCover","Linear.HomogeneousRatioFieldMap","Linear.HomogeneousRationalIdeal","Linear.HomogeneousRationalPullback","Linear.InjectiveCochainCocycleSourceClass","Linear.InjectiveCochainDegreeZeroClass","Linear.InjectiveCocycleExtPresentation","Linear.InjectiveCocycleSourceNaturality","Linear.InjectiveCocycleTransport","Linear.InjectiveNativeDegreeZeroClass","Linear.IntegerGradedFiniteFreeSurjection","Linear.IntegerGradedFinitePresentation","Linear.IntegerGradedFiniteRelations","Linear.IntegerGradedHomogeneousAnnihilator","Linear.IntegerGradedKernelGenerators","Linear.IntegerGradedModuleGenerators","Linear.IntegerGradedModuleProjection","Linear.IntegerGradedRingProduct","Linear.IntegerGradedSubmoduleDecomposition","Linear.IntegerGradedSurjectionPreimage","Linear.IntegerGradingShift","Linear.IntegerShiftedFreeDecomposition","Linear.IntegerShiftedFreeDualRelations","Linear.IntegerShiftedFreeGeneralRelationPi","Linear.IntegerShiftedFreeGeneratorMap","Linear.IntegerShiftedFreeGradedDualRelation","Linear.IntegerShiftedFreeHomCoordinates","Linear.IntegerShiftedFreeHomPiCoordinates","Linear.IntegerShiftedFreeMatrix","Linear.IntegerShiftedFreePieces","Linear.IntegerShiftedFreeRegradingPresentation","Linear.IntegralKrullDimension","Linear.Iteration","Linear.JacobianNonzero","Linear.JacobianSpecialization","Linear.JacobianTrace","Linear.KoszulComparison","Linear.KoszulCoordinateEntryNaturality","Linear.KoszulCoordinateWholeNaturality","Linear.KoszulExactResolution","Linear.KoszulFunctionResolution","Linear.KoszulFunctionUnit","Linear.KoszulFunctionUnitAllDegrees","Linear.KoszulHomogeneousCoordinates","Linear.KoszulHomotopyTop","Linear.KoszulLocalGlobalExact","Linear.KoszulResolution","Linear.KoszulRingEquivExact","Linear.KoszulSocleDeterminant","Linear.KoszulSocleMap","Linear.KoszulTop","Linear.KoszulTopComplementFunctional","Linear.KoszulTopHomCoefficientRestriction","Linear.KoszulUnitExactness","Linear.LiftedParameterCoordinates","Linear.LiftedParameterMaps","Linear.LiftedParameterPresentation","Linear.LiftedParametersRegular"]
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
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
