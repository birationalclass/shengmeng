module
import all Linear.ProjectiveConeSurjectivity
import all Linear.ProjectiveCoordinateDomainMap
import all Linear.ProjectiveCoordinateFractionMap
import all Linear.ProjectiveCoordinateHilbertGrowth
import all Linear.ProjectiveCoordinateRatioMap
import all Linear.ProjectiveCoordinateUnramified
import all Linear.ProjectiveCutAffineKoszul
import all Linear.ProjectiveCutAllPrimeKoszul
import all Linear.ProjectiveCutKoszulQuotient
import all Linear.ProjectiveCutOutsideExact
import all Linear.ProjectiveDifferentialDimension
import all Linear.ProjectiveFiberChartAvoidance
import all Linear.ProjectiveFibersFinite
import all Linear.ProjectiveFilteredCombination
import all Linear.ProjectiveFilteredPullback
import all Linear.ProjectiveFilteredReflection
import all Linear.ProjectiveFilteredUpperBound
import all Linear.ProjectiveGeneralReducedFibers
import all Linear.ProjectiveGenericGrowthComparison
import all Linear.ProjectiveGenericGrowthDegree
import all Linear.ProjectiveGenericHomogeneousBasis
import all Linear.ProjectiveGoodAffineCoordinates
import all Linear.ProjectiveGradedPullback
import all Linear.ProjectiveHomogeneousChartAvoidance
import all Linear.ProjectiveHomogeneousCoefficientBound
import all Linear.ProjectiveHomogeneousGenericControl
import all Linear.ProjectiveHomogeneousModuleGenerators
import all Linear.ProjectiveIdealInvariance
import all Linear.ProjectiveLinearNormalization
import all Linear.ProjectiveLinearProjectionTensorFibers
import all Linear.ProjectiveLinearSectionClosedReduced
import all Linear.ProjectiveLinearSectionDegree
import all Linear.ProjectiveLinearSectionEquationFibers
import all Linear.ProjectiveLinearSectionFinitePullback
import all Linear.ProjectiveLinearSectionPointEquiv
import all Linear.ProjectiveLinearSectionReducedPullbackOpen
import all Linear.ProjectiveNormalizedConePoint
import all Linear.ProjectivePullbackAllComponents
import all Linear.ProjectivePulledGlobalCokernelWholeCutNativeTwist
import all Linear.ProjectivePulledGlobalCokernelWholeCutPushforward
import all Linear.ProjectivePulledKoszulChartExactTransfer
import all Linear.ProjectivePulledKoszulGlobalCokernelAugmentation
import all Linear.ProjectivePulledKoszulGlobalCokernelChartPushforward
import all Linear.ProjectivePulledKoszulGlobalExact
import all Linear.ProjectivePulledKoszulNativeChartExact
import all Linear.ProjectivePulledKoszulNativeSheafExact
import all Linear.ProjectivePulledKoszulOriginalAmbientCover
import all Linear.ProjectivePulledKoszulSupportedCokernelUnit
import all Linear.ProjectivePulledLinearKoszulAffineStandard
import all Linear.ProjectivePulledLinearKoszulForms
import all Linear.ProjectivePulledLinearKoszulGlobal
import all Linear.ProjectivePulledNativeChartCutEmbedding
import all Linear.ProjectivePulledNativeChartCutQuotientFactor
import all Linear.ProjectivePulledOriginalChainWholeCutExtClass
import all Linear.ProjectivePulledOriginalChartDataCutStatement
import all Linear.ProjectivePulledOriginalChartDataCutZero
import all Linear.ProjectivePulledOriginalChartIntrinsicMapZero
import all Linear.ProjectivePulledOriginalChartPresentation
import all Linear.ProjectivePulledOriginalExactChartData
import all Linear.ProjectivePulledOriginalKoszulAboveRank
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.ProjectiveConeSurjectivity","Linear.ProjectiveCoordinateDomainMap","Linear.ProjectiveCoordinateFractionMap","Linear.ProjectiveCoordinateHilbertGrowth","Linear.ProjectiveCoordinateRatioMap","Linear.ProjectiveCoordinateUnramified","Linear.ProjectiveCutAffineKoszul","Linear.ProjectiveCutAllPrimeKoszul","Linear.ProjectiveCutKoszulQuotient","Linear.ProjectiveCutOutsideExact","Linear.ProjectiveDifferentialDimension","Linear.ProjectiveFiberChartAvoidance","Linear.ProjectiveFibersFinite","Linear.ProjectiveFilteredCombination","Linear.ProjectiveFilteredPullback","Linear.ProjectiveFilteredReflection","Linear.ProjectiveFilteredUpperBound","Linear.ProjectiveGeneralReducedFibers","Linear.ProjectiveGenericGrowthComparison","Linear.ProjectiveGenericGrowthDegree","Linear.ProjectiveGenericHomogeneousBasis","Linear.ProjectiveGoodAffineCoordinates","Linear.ProjectiveGradedPullback","Linear.ProjectiveHomogeneousChartAvoidance","Linear.ProjectiveHomogeneousCoefficientBound","Linear.ProjectiveHomogeneousGenericControl","Linear.ProjectiveHomogeneousModuleGenerators","Linear.ProjectiveIdealInvariance","Linear.ProjectiveLinearNormalization","Linear.ProjectiveLinearProjectionTensorFibers","Linear.ProjectiveLinearSectionClosedReduced","Linear.ProjectiveLinearSectionDegree","Linear.ProjectiveLinearSectionEquationFibers","Linear.ProjectiveLinearSectionFinitePullback","Linear.ProjectiveLinearSectionPointEquiv","Linear.ProjectiveLinearSectionReducedPullbackOpen","Linear.ProjectiveNormalizedConePoint","Linear.ProjectivePullbackAllComponents","Linear.ProjectivePulledGlobalCokernelWholeCutNativeTwist","Linear.ProjectivePulledGlobalCokernelWholeCutPushforward","Linear.ProjectivePulledKoszulChartExactTransfer","Linear.ProjectivePulledKoszulGlobalCokernelAugmentation","Linear.ProjectivePulledKoszulGlobalCokernelChartPushforward","Linear.ProjectivePulledKoszulGlobalExact","Linear.ProjectivePulledKoszulNativeChartExact","Linear.ProjectivePulledKoszulNativeSheafExact","Linear.ProjectivePulledKoszulOriginalAmbientCover","Linear.ProjectivePulledKoszulSupportedCokernelUnit","Linear.ProjectivePulledLinearKoszulAffineStandard","Linear.ProjectivePulledLinearKoszulForms","Linear.ProjectivePulledLinearKoszulGlobal","Linear.ProjectivePulledNativeChartCutEmbedding","Linear.ProjectivePulledNativeChartCutQuotientFactor","Linear.ProjectivePulledOriginalChainWholeCutExtClass","Linear.ProjectivePulledOriginalChartDataCutStatement","Linear.ProjectivePulledOriginalChartDataCutZero","Linear.ProjectivePulledOriginalChartIntrinsicMapZero","Linear.ProjectivePulledOriginalChartPresentation","Linear.ProjectivePulledOriginalExactChartData","Linear.ProjectivePulledOriginalKoszulAboveRank"]
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
