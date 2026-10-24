module
import all Linear.NativeProjectiveHomogeneousSurjection
import all Linear.NativeProjectiveIntegerTwistChartFree
import all Linear.NativeProjectiveKernelFraction
import all Linear.NativeProjectiveKernelGrading
import all Linear.NativeProjectiveKernelLocalLift
import all Linear.NativeProjectiveKernelSectionExact
import all Linear.NativeProjectiveKernelSheaf
import all Linear.NativeProjectiveKernelTwistFinitePresentation
import all Linear.NativeProjectiveLaurentComplex
import all Linear.NativeProjectiveLaurentFactors
import all Linear.NativeProjectiveLaurentInitial
import all Linear.NativeProjectiveLaurentNoninitial
import all Linear.NativeProjectiveLaurentTransition
import all Linear.NativeProjectiveMatrixHomology
import all Linear.NativeProjectiveModuleBaseScalarValue
import all Linear.NativeProjectiveModuleFractionLift
import all Linear.NativeProjectiveModuleLocalAdd
import all Linear.NativeProjectiveModuleLocalMap
import all Linear.NativeProjectiveModuleLocalPredicate
import all Linear.NativeProjectiveModuleLocalSMul
import all Linear.NativeProjectiveModulePresheaf
import all Linear.NativeProjectiveModuleScalarApply
import all Linear.NativeProjectiveModuleSections
import all Linear.NativeProjectiveModuleSheaf
import all Linear.NativeProjectiveModuleSheafEpi
import all Linear.NativeProjectiveModuleSheafMap
import all Linear.NativeProjectiveOrderedCechExact
import all Linear.NativeProjectiveOverCokernel
import all Linear.NativeProjectivePrimeMapExact
import all Linear.NativeProjectivePrimeTwistUnit
import all Linear.NativeProjectiveRingIntegerPieces
import all Linear.NativeProjectiveRingModuleLocalization
import all Linear.NativeProjectiveSheafExact
import all Linear.NativeProjectiveShiftedFreeBiproduct
import all Linear.NativeProjectiveShiftedFreeChart
import all Linear.NativeProjectiveShiftedFreeCoordinateMaps
import all Linear.NativeProjectiveShiftedFreePrimeIdentities
import all Linear.NativeProjectiveShiftedFreeSheafIdentities
import all Linear.NativeProjectiveShiftedFreeSheafMaps
import all Linear.NativeProjectiveTwistCechVanishing
import all Linear.NativeProjectiveTwistChartFree
import all Linear.NativeProjectiveTwistFinitePresentation
import all Linear.NativeProjectiveTwistFraction
import all Linear.NativeProjectiveTwistQuasicoherent
import all Linear.NativeProjectiveTwistRegrading
import all Linear.NativeProjectiveTwistSectionEquiv
import all Linear.NativeProjectiveTwistSheafOverIso
import all Linear.NativeScaledMonomialCechNaturality
import all Linear.NativeScaledMonomialMultiplicationLaurent
import all Linear.NativeScaledMonomialTopDuality
import all Linear.NativeShiftedFreeChartSectionsSurjective
import all Linear.NativeShiftedFreePresentationTopCechCokernel
import all Linear.NativeShiftedFreeSheafBiproductMap
import all Linear.NativeShiftedFreeSheafMatrixEntry
import all Linear.NativeShiftedFreeSheafMatrixZero
import all Linear.NativeShiftedFreeSheafScalarEntry
import all Linear.NativeShiftedFreeSheafScalarMatrix
import all Linear.NativeSourceSpecChartLinear
import all Linear.NativeSourceSpecOpenSectionsModule
import all Linear.NativeSpecifiedNormalizationActualTopDuality
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeProjectiveHomogeneousSurjection","Linear.NativeProjectiveIntegerTwistChartFree","Linear.NativeProjectiveKernelFraction","Linear.NativeProjectiveKernelGrading","Linear.NativeProjectiveKernelLocalLift","Linear.NativeProjectiveKernelSectionExact","Linear.NativeProjectiveKernelSheaf","Linear.NativeProjectiveKernelTwistFinitePresentation","Linear.NativeProjectiveLaurentComplex","Linear.NativeProjectiveLaurentFactors","Linear.NativeProjectiveLaurentInitial","Linear.NativeProjectiveLaurentNoninitial","Linear.NativeProjectiveLaurentTransition","Linear.NativeProjectiveMatrixHomology","Linear.NativeProjectiveModuleBaseScalarValue","Linear.NativeProjectiveModuleFractionLift","Linear.NativeProjectiveModuleLocalAdd","Linear.NativeProjectiveModuleLocalMap","Linear.NativeProjectiveModuleLocalPredicate","Linear.NativeProjectiveModuleLocalSMul","Linear.NativeProjectiveModulePresheaf","Linear.NativeProjectiveModuleScalarApply","Linear.NativeProjectiveModuleSections","Linear.NativeProjectiveModuleSheaf","Linear.NativeProjectiveModuleSheafEpi","Linear.NativeProjectiveModuleSheafMap","Linear.NativeProjectiveOrderedCechExact","Linear.NativeProjectiveOverCokernel","Linear.NativeProjectivePrimeMapExact","Linear.NativeProjectivePrimeTwistUnit","Linear.NativeProjectiveRingIntegerPieces","Linear.NativeProjectiveRingModuleLocalization","Linear.NativeProjectiveSheafExact","Linear.NativeProjectiveShiftedFreeBiproduct","Linear.NativeProjectiveShiftedFreeChart","Linear.NativeProjectiveShiftedFreeCoordinateMaps","Linear.NativeProjectiveShiftedFreePrimeIdentities","Linear.NativeProjectiveShiftedFreeSheafIdentities","Linear.NativeProjectiveShiftedFreeSheafMaps","Linear.NativeProjectiveTwistCechVanishing","Linear.NativeProjectiveTwistChartFree","Linear.NativeProjectiveTwistFinitePresentation","Linear.NativeProjectiveTwistFraction","Linear.NativeProjectiveTwistQuasicoherent","Linear.NativeProjectiveTwistRegrading","Linear.NativeProjectiveTwistSectionEquiv","Linear.NativeProjectiveTwistSheafOverIso","Linear.NativeScaledMonomialCechNaturality","Linear.NativeScaledMonomialMultiplicationLaurent","Linear.NativeScaledMonomialTopDuality","Linear.NativeShiftedFreeChartSectionsSurjective","Linear.NativeShiftedFreePresentationTopCechCokernel","Linear.NativeShiftedFreeSheafBiproductMap","Linear.NativeShiftedFreeSheafMatrixEntry","Linear.NativeShiftedFreeSheafMatrixZero","Linear.NativeShiftedFreeSheafScalarEntry","Linear.NativeShiftedFreeSheafScalarMatrix","Linear.NativeSourceSpecChartLinear","Linear.NativeSourceSpecOpenSectionsModule","Linear.NativeSpecifiedNormalizationActualTopDuality"]
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
