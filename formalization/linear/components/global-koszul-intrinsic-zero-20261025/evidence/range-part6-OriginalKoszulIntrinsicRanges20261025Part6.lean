module
import all Linear.NativeKoszulOffCutRestrictionExact
import all Linear.NativeKoszulOffCutSectionExact
import all Linear.NativeKoszulPresentationDataObjects
import all Linear.NativeKoszulStandardAffineNamedTarget
import all Linear.NativeKoszulSupportedCokernelUnit
import all Linear.NativeProjectiveChart
import all Linear.NativeProjectiveChartClosedPullback
import all Linear.NativeProjectiveChartPullback
import all Linear.NativeProjectiveChartSectionReduced
import all Linear.NativeProjectiveDegreeOneCover
import all Linear.NativeProjectiveDegreeZeroComposition
import all Linear.NativeProjectiveDegreeZeroEpi
import all Linear.NativeProjectiveDegreeZeroIdentities
import all Linear.NativeProjectiveDegreeZeroMap
import all Linear.NativeProjectiveExactFinitePresentation
import all Linear.NativeProjectiveFiniteGradedChartPresentation
import all Linear.NativeProjectiveFiniteGradedQuasicoherent
import all Linear.NativeProjectiveHomogeneousSMul
import all Linear.NativeProjectiveIntegerTwistChartFree
import all Linear.NativeProjectiveKernelFraction
import all Linear.NativeProjectiveKernelGrading
import all Linear.NativeProjectiveKernelLocalLift
import all Linear.NativeProjectiveKernelSectionExact
import all Linear.NativeProjectiveKernelSheaf
import all Linear.NativeProjectiveKoszulComplex
import all Linear.NativeProjectiveKoszulTermInternalExtVanishing
import all Linear.NativeProjectiveModuleFractionLift
import all Linear.NativeProjectiveModuleLocalAdd
import all Linear.NativeProjectiveModuleLocalMap
import all Linear.NativeProjectiveModuleLocalPredicate
import all Linear.NativeProjectiveModuleLocalSMul
import all Linear.NativeProjectiveModulePresheaf
import all Linear.NativeProjectiveModuleSections
import all Linear.NativeProjectiveModuleSheaf
import all Linear.NativeProjectiveModuleSheafMap
import all Linear.NativeProjectiveOpenKoszulExactChart
import all Linear.NativeProjectiveOpenKoszulExactChartObjects
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
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeKoszulOffCutRestrictionExact","Linear.NativeKoszulOffCutSectionExact","Linear.NativeKoszulPresentationDataObjects","Linear.NativeKoszulStandardAffineNamedTarget","Linear.NativeKoszulSupportedCokernelUnit","Linear.NativeProjectiveChart","Linear.NativeProjectiveChartClosedPullback","Linear.NativeProjectiveChartPullback","Linear.NativeProjectiveChartSectionReduced","Linear.NativeProjectiveDegreeOneCover","Linear.NativeProjectiveDegreeZeroComposition","Linear.NativeProjectiveDegreeZeroEpi","Linear.NativeProjectiveDegreeZeroIdentities","Linear.NativeProjectiveDegreeZeroMap","Linear.NativeProjectiveExactFinitePresentation","Linear.NativeProjectiveFiniteGradedChartPresentation","Linear.NativeProjectiveFiniteGradedQuasicoherent","Linear.NativeProjectiveHomogeneousSMul","Linear.NativeProjectiveIntegerTwistChartFree","Linear.NativeProjectiveKernelFraction","Linear.NativeProjectiveKernelGrading","Linear.NativeProjectiveKernelLocalLift","Linear.NativeProjectiveKernelSectionExact","Linear.NativeProjectiveKernelSheaf","Linear.NativeProjectiveKoszulComplex","Linear.NativeProjectiveKoszulTermInternalExtVanishing","Linear.NativeProjectiveModuleFractionLift","Linear.NativeProjectiveModuleLocalAdd","Linear.NativeProjectiveModuleLocalMap","Linear.NativeProjectiveModuleLocalPredicate","Linear.NativeProjectiveModuleLocalSMul","Linear.NativeProjectiveModulePresheaf","Linear.NativeProjectiveModuleSections","Linear.NativeProjectiveModuleSheaf","Linear.NativeProjectiveModuleSheafMap","Linear.NativeProjectiveOpenKoszulExactChart","Linear.NativeProjectiveOpenKoszulExactChartObjects","Linear.NativeProjectiveOverCokernel","Linear.NativeProjectivePrimeMapExact","Linear.NativeProjectivePrimeTwistUnit","Linear.NativeProjectiveRingIntegerPieces","Linear.NativeProjectiveRingModuleLocalization","Linear.NativeProjectiveSheafExact","Linear.NativeProjectiveShiftedFreeBiproduct","Linear.NativeProjectiveShiftedFreeChart","Linear.NativeProjectiveShiftedFreeCoordinateMaps","Linear.NativeProjectiveShiftedFreePrimeIdentities","Linear.NativeProjectiveShiftedFreeSheafIdentities","Linear.NativeProjectiveShiftedFreeSheafMaps","Linear.NativeProjectiveTwistChartFree","Linear.NativeProjectiveTwistFraction","Linear.NativeProjectiveTwistRegrading","Linear.NativeProjectiveTwistSectionEquiv","Linear.NativeProjectiveTwistSheafOverIso","Linear.NativeShiftedFreeIntegerTwistBiproduct","Linear.NativeShiftedFreeSheafMatrixEntry","Linear.NativeStructureModuleFraction","Linear.NativeStructureModuleSections","Linear.NativeStructureModuleSheaf","Linear.NativeTwistRegradingMapNaturality"]
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
