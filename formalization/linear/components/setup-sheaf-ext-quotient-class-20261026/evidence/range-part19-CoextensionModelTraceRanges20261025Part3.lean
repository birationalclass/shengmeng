module
import all Linear.GenericUnramifiedOpen
import all Linear.GlobalDiagonalNormalization
import all Linear.GradedDecompositionTransport
import all Linear.GradedHomComponent
import all Linear.GradedHomComponentNonzero
import all Linear.GradedHomDecomposition
import all Linear.GradedHomFiniteSupport
import all Linear.GradedHomPiece
import all Linear.GradedHomProjection
import all Linear.GradedIntegerProjection
import all Linear.GradedIntegerProjector
import all Linear.GradedModuleHomogeneousGenerators
import all Linear.GradedModuleProjection
import all Linear.HomogeneousChartOverlapValue
import all Linear.HomogeneousCoordinateGrading
import all Linear.HomogeneousCoordinatePieces
import all Linear.HomogeneousLocalizationRefinementValue
import all Linear.HomogeneousPullbackComponents
import all Linear.HomogeneousQuotient
import all Linear.HomogeneousRatioFieldMap
import all Linear.HomogeneousRationalIdeal
import all Linear.HomogeneousRationalPullback
import all Linear.HomologicalComplexScalarHomology
import all Linear.InjectiveClosedClassExtAcyclic
import all Linear.IntegerGradedEndZero
import all Linear.IntegerGradedFiniteFreeSurjection
import all Linear.IntegerGradedFinitePresentation
import all Linear.IntegerGradedFinitePresentationData
import all Linear.IntegerGradedFiniteRelations
import all Linear.IntegerGradedHomEvaluationCoordinates
import all Linear.IntegerGradedHomPieceFinite
import all Linear.IntegerGradedHomPrecomposition
import all Linear.IntegerGradedHomPrecompositionIdentity
import all Linear.IntegerGradedHomogeneousAnnihilator
import all Linear.IntegerGradedKernelGenerators
import all Linear.IntegerGradedModuleGenerators
import all Linear.IntegerGradedModuleProjection
import all Linear.IntegerGradedRingProduct
import all Linear.IntegerGradedSubmoduleDecomposition
import all Linear.IntegerGradedSurjectionPreimage
import all Linear.IntegerGradingShift
import all Linear.IntegerHomEvaluationMapLiftSquare
import all Linear.IntegerPresentationDataCoordinateDuality
import all Linear.IntegerPresentationDataCoordinateIndependence
import all Linear.IntegerPresentationDataCoordinateNaturality
import all Linear.IntegerShiftedFreeDecomposition
import all Linear.IntegerShiftedFreeDualRegrading
import all Linear.IntegerShiftedFreeDualRelations
import all Linear.IntegerShiftedFreeGeneralDualMatrix
import all Linear.IntegerShiftedFreeGeneralRelationBiproduct
import all Linear.IntegerShiftedFreeGeneralRelationPi
import all Linear.IntegerShiftedFreeGeneratorMap
import all Linear.IntegerShiftedFreeGradedDualRelation
import all Linear.IntegerShiftedFreeHomCoordinates
import all Linear.IntegerShiftedFreeHomPiCoordinates
import all Linear.IntegerShiftedFreeHomogeneousMapLift
import all Linear.IntegerShiftedFreeMatrix
import all Linear.IntegerShiftedFreePieces
import all Linear.IntegerShiftedFreePresentationDualCokernel
import all Linear.IntegerShiftedFreePresentationHomKernelCoordinates
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.GenericUnramifiedOpen","Linear.GlobalDiagonalNormalization","Linear.GradedDecompositionTransport","Linear.GradedHomComponent","Linear.GradedHomComponentNonzero","Linear.GradedHomDecomposition","Linear.GradedHomFiniteSupport","Linear.GradedHomPiece","Linear.GradedHomProjection","Linear.GradedIntegerProjection","Linear.GradedIntegerProjector","Linear.GradedModuleHomogeneousGenerators","Linear.GradedModuleProjection","Linear.HomogeneousChartOverlapValue","Linear.HomogeneousCoordinateGrading","Linear.HomogeneousCoordinatePieces","Linear.HomogeneousLocalizationRefinementValue","Linear.HomogeneousPullbackComponents","Linear.HomogeneousQuotient","Linear.HomogeneousRatioFieldMap","Linear.HomogeneousRationalIdeal","Linear.HomogeneousRationalPullback","Linear.HomologicalComplexScalarHomology","Linear.InjectiveClosedClassExtAcyclic","Linear.IntegerGradedEndZero","Linear.IntegerGradedFiniteFreeSurjection","Linear.IntegerGradedFinitePresentation","Linear.IntegerGradedFinitePresentationData","Linear.IntegerGradedFiniteRelations","Linear.IntegerGradedHomEvaluationCoordinates","Linear.IntegerGradedHomPieceFinite","Linear.IntegerGradedHomPrecomposition","Linear.IntegerGradedHomPrecompositionIdentity","Linear.IntegerGradedHomogeneousAnnihilator","Linear.IntegerGradedKernelGenerators","Linear.IntegerGradedModuleGenerators","Linear.IntegerGradedModuleProjection","Linear.IntegerGradedRingProduct","Linear.IntegerGradedSubmoduleDecomposition","Linear.IntegerGradedSurjectionPreimage","Linear.IntegerGradingShift","Linear.IntegerHomEvaluationMapLiftSquare","Linear.IntegerPresentationDataCoordinateDuality","Linear.IntegerPresentationDataCoordinateIndependence","Linear.IntegerPresentationDataCoordinateNaturality","Linear.IntegerShiftedFreeDecomposition","Linear.IntegerShiftedFreeDualRegrading","Linear.IntegerShiftedFreeDualRelations","Linear.IntegerShiftedFreeGeneralDualMatrix","Linear.IntegerShiftedFreeGeneralRelationBiproduct","Linear.IntegerShiftedFreeGeneralRelationPi","Linear.IntegerShiftedFreeGeneratorMap","Linear.IntegerShiftedFreeGradedDualRelation","Linear.IntegerShiftedFreeHomCoordinates","Linear.IntegerShiftedFreeHomPiCoordinates","Linear.IntegerShiftedFreeHomogeneousMapLift","Linear.IntegerShiftedFreeMatrix","Linear.IntegerShiftedFreePieces","Linear.IntegerShiftedFreePresentationDualCokernel","Linear.IntegerShiftedFreePresentationHomKernelCoordinates"]
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
