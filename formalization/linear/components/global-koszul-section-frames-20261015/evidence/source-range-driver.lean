module
import all Linear.ActualPresentationDualKernel
import all Linear.ActualPresentationGradedDualKernel
import all Linear.GradedIntegerProjection
import all Linear.GradedIntegerProjector
import all Linear.GradedModuleProjection
import all Linear.IntegerGradedKernelGenerators
import all Linear.IntegerGradedModuleGenerators
import all Linear.IntegerGradedModuleProjection
import all Linear.IntegerGradedRingProduct
import all Linear.IntegerGradedSubmoduleDecomposition
import all Linear.IntegerGradedSurjectionPreimage
import all Linear.IntegerGradingShift
import all Linear.IntegerShiftedFreeDualRelations
import all Linear.IntegerShiftedFreeGeneralRelationPi
import all Linear.IntegerShiftedFreeGradedDualRelation
import all Linear.IntegerShiftedFreeHomCoordinates
import all Linear.IntegerShiftedFreeHomPiCoordinates
import all Linear.IntegerShiftedFreeMatrix
import all Linear.IntegerShiftedFreePieces
import all Linear.IntegerShiftedFreeRegradingPresentation
import all Linear.KoszulHomogeneousCoordinates
import all Linear.NativeGlobalKoszulFrameEntries
import all Linear.NativeGlobalKoszulSectionMatrix
import all Linear.NativeHomogeneousGlobalSection
import all Linear.NativeHomogeneousIntegerFrameMultiply
import all Linear.NativeHomogeneousSectionFrame
import all Linear.NativeIntegerFreeTwistRegrading
import all Linear.NativeIntegerPrimeTwist
import all Linear.NativeIntegerShiftedFreeBicone
import all Linear.NativeIntegerShiftedFreeCoordinateMaps
import all Linear.NativeIntegerShiftedFreeSectionFrames
import all Linear.NativeIntegerTwistDegreeTransport
import all Linear.NativeIntegerTwistScalarCommute
import all Linear.NativeIntegerTwistSectionFrames
import all Linear.NativeProjectiveDegreeZeroComposition
import all Linear.NativeProjectiveDegreeZeroIdentities
import all Linear.NativeProjectiveDegreeZeroMap
import all Linear.NativeProjectiveHomogeneousSMul
import all Linear.NativeProjectiveIntegerTwistChartFree
import all Linear.NativeProjectiveKoszulComplex
import all Linear.NativeProjectiveModuleLocalAdd
import all Linear.NativeProjectiveModuleLocalMap
import all Linear.NativeProjectiveModuleLocalPredicate
import all Linear.NativeProjectiveModuleLocalSMul
import all Linear.NativeProjectiveModulePresheaf
import all Linear.NativeProjectiveModuleSections
import all Linear.NativeProjectiveModuleSheaf
import all Linear.NativeProjectiveModuleSheafMap
import all Linear.NativeProjectivePrimeTwistUnit
import all Linear.NativeProjectiveRingIntegerPieces
import all Linear.NativeProjectiveRingModuleLocalization
import all Linear.NativeProjectiveShiftedFreeBiproduct
import all Linear.NativeProjectiveShiftedFreeCoordinateMaps
import all Linear.NativeProjectiveShiftedFreePrimeIdentities
import all Linear.NativeProjectiveShiftedFreeSheafIdentities
import all Linear.NativeProjectiveShiftedFreeSheafMaps
import all Linear.NativeProjectiveTwistChartFree
import all Linear.NativeProjectiveTwistFraction
import all Linear.NativeProjectiveTwistRegrading
import all Linear.NativeProjectiveTwistSectionEquiv
import all Linear.NativeProjectiveTwistSheafOverIso
import all Linear.NativeShiftedFreeIntegerTwistBiproduct
import all Linear.NativeShiftedFreeSheafMatrixEntry
import all Linear.NativeStructureModuleFraction
import all Linear.NativeStructureModuleSections
import all Linear.NativeStructureModuleSheaf
import all Linear.NativeTwistRegradingMapNaturality
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomPrecompose
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleInternalHomComplex
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
  if count <= 23 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
