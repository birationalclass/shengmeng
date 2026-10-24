module
import all Linear.ProjectivePulledOriginalKoszulInternalExtVanishing
import all Linear.ProjectivePulledOriginalKoszulTopBoundary
import all Linear.ProjectivePulledOriginalNamedExactChart
import all Linear.ProjectivePulledOriginalSetupIntrinsicZeroFamily
import all Linear.ProjectivePulledOriginalSetupResolution
import all Linear.ProjectivePulledOriginalSetupWholeTopCokernelFamily
import all Linear.ProjectivePulledOriginalSetupWholeTopCokernelLambdaFamily
import all Linear.ProjectivePulledOriginalWholeTopCokernelStatement
import all Linear.ProjectivePulledSectionAffineComparison
import all Linear.ProjectivePulledSectionClosedEmbedding
import all Linear.ProjectivePulledSectionGlobalReduced
import all Linear.ProjectivePulledSectionNativeCoverage
import all Linear.ProjectivePulledSectionSmoothPoints
import all Linear.ProjectivePulledWholeCokernelLambdaFamily
import all Linear.ProjectivePulledWholeCokernelLambdaStatement
import all Linear.ProjectivePulledWholeCutArtinian
import all Linear.ProjectivePulledWholeCutNativeTwistQuotientAugmentation
import all Linear.ProjectivePulledWholeCutOriginalEmbedding
import all Linear.ProjectivePulledWholeCutResolutionObjects
import all Linear.ProjectiveRatioChartKernel
import all Linear.ProjectiveRationalChart
import all Linear.ProjectiveRationalInvariance
import all Linear.ProjectiveRegularCutOpen
import all Linear.ProjectiveScalingFixedRatios
import all Linear.ProjectiveScalingMap
import all Linear.ProjectiveSectionDefiningForms
import all Linear.ProjectiveSmoothCommonDimension
import all Linear.ProjectiveSmoothCutRegular
import all Linear.ProjectiveSmoothOpenPoint
import all Linear.ProjectiveSmoothPointParameters
import all Linear.ProjectiveTargetGoodLoci
import all Linear.ProjectiveTargetGoodOpen
import all Linear.ProjectiveVarietyLocalCutRegular
import all Linear.ProjectiveWholeFiberChart
import all Linear.ProjectiveWholeFiberGoodPoint
import all Linear.ProjectiveWholeFiberPointCount
import all Linear.ProjectiveWholeFiberPointLoci
import all Linear.ProjectiveWholeReducedFiber
import all Linear.QuotientAwayAtUnit
import all Linear.QuotientClosedBaseChange
import all Linear.QuotientHilbertKrullDimension
import all Linear.QuotientLocalPullbackComparison
import all Linear.QuotientNormalizationFilteredLower
import all Linear.QuotientNormalizationFilteredUpper
import all Linear.RationalLocalEssentialFiniteType
import all Linear.RationalPointLocalMap
import all Linear.RationalPointLocalization
import all Linear.RationalPointUnramifiedComposition
import all Linear.RectangularMinor
import all Linear.ReducedClosedBaseChange
import all Linear.ReducedPolynomialProjectionFibers
import all Linear.Reduction
import all Linear.RegularGeneratorsFree
import all Linear.RegularSpecialization
import all Linear.RelativeJacobian
import all Linear.RelativeJacobianTrace
import all Linear.ResiduePairing
import all Linear.RingEquivOriginalQuotientFactor
import all Linear.ScalingOrbitTranscendental
import all Linear.SchemeModuleActualStalkExact
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.ProjectivePulledOriginalKoszulInternalExtVanishing","Linear.ProjectivePulledOriginalKoszulTopBoundary","Linear.ProjectivePulledOriginalNamedExactChart","Linear.ProjectivePulledOriginalSetupIntrinsicZeroFamily","Linear.ProjectivePulledOriginalSetupResolution","Linear.ProjectivePulledOriginalSetupWholeTopCokernelFamily","Linear.ProjectivePulledOriginalSetupWholeTopCokernelLambdaFamily","Linear.ProjectivePulledOriginalWholeTopCokernelStatement","Linear.ProjectivePulledSectionAffineComparison","Linear.ProjectivePulledSectionClosedEmbedding","Linear.ProjectivePulledSectionGlobalReduced","Linear.ProjectivePulledSectionNativeCoverage","Linear.ProjectivePulledSectionSmoothPoints","Linear.ProjectivePulledWholeCokernelLambdaFamily","Linear.ProjectivePulledWholeCokernelLambdaStatement","Linear.ProjectivePulledWholeCutArtinian","Linear.ProjectivePulledWholeCutNativeTwistQuotientAugmentation","Linear.ProjectivePulledWholeCutOriginalEmbedding","Linear.ProjectivePulledWholeCutResolutionObjects","Linear.ProjectiveRatioChartKernel","Linear.ProjectiveRationalChart","Linear.ProjectiveRationalInvariance","Linear.ProjectiveRegularCutOpen","Linear.ProjectiveScalingFixedRatios","Linear.ProjectiveScalingMap","Linear.ProjectiveSectionDefiningForms","Linear.ProjectiveSmoothCommonDimension","Linear.ProjectiveSmoothCutRegular","Linear.ProjectiveSmoothOpenPoint","Linear.ProjectiveSmoothPointParameters","Linear.ProjectiveTargetGoodLoci","Linear.ProjectiveTargetGoodOpen","Linear.ProjectiveVarietyLocalCutRegular","Linear.ProjectiveWholeFiberChart","Linear.ProjectiveWholeFiberGoodPoint","Linear.ProjectiveWholeFiberPointCount","Linear.ProjectiveWholeFiberPointLoci","Linear.ProjectiveWholeReducedFiber","Linear.QuotientAwayAtUnit","Linear.QuotientClosedBaseChange","Linear.QuotientHilbertKrullDimension","Linear.QuotientLocalPullbackComparison","Linear.QuotientNormalizationFilteredLower","Linear.QuotientNormalizationFilteredUpper","Linear.RationalLocalEssentialFiniteType","Linear.RationalPointLocalMap","Linear.RationalPointLocalization","Linear.RationalPointUnramifiedComposition","Linear.RectangularMinor","Linear.ReducedClosedBaseChange","Linear.ReducedPolynomialProjectionFibers","Linear.Reduction","Linear.RegularGeneratorsFree","Linear.RegularSpecialization","Linear.RelativeJacobian","Linear.RelativeJacobianTrace","Linear.ResiduePairing","Linear.RingEquivOriginalQuotientFactor","Linear.ScalingOrbitTranscendental","Linear.SchemeModuleActualStalkExact"]
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
