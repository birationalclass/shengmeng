module
import all Linear.PolynomialPointEvaluation
import all Linear.PolynomialProjectionFiberQuotient
import all Linear.PolynomialRecentering
import all Linear.PolynomialRectangleDimension
import all Linear.PolynomialReducedPointCount
import all Linear.PolynomialRegular
import all Linear.PolynomialSmoothCoordinates
import all Linear.PolynomialSmoothReduction
import all Linear.PolynomialSocle
import all Linear.PolynomialTotalDegreeHilbert
import all Linear.PowerSeriesAugmentation
import all Linear.PowerSeriesCentering
import all Linear.PowerSeriesCoefficients
import all Linear.PowerSeriesCoordinateChart
import all Linear.PowerSeriesDerivative
import all Linear.PowerSeriesDiagonal
import all Linear.PowerSeriesFlatten
import all Linear.PowerSeriesFlattenDerivative
import all Linear.PowerSeriesRegular
import all Linear.PowerSeriesSocle
import all Linear.PowerSeriesSpecialization
import all Linear.PowerSeriesTranslation
import all Linear.Primitive
import all Linear.Projective
import all Linear.ProjectiveAffineFiberClosedPullback
import all Linear.ProjectiveAffineFiberFinite
import all Linear.ProjectiveAffineFiberMap
import all Linear.ProjectiveAffineFiberPointEquiv
import all Linear.ProjectiveAffineFiberReduced
import all Linear.ProjectiveAffineFiberUnit
import all Linear.ProjectiveAffineFiberUniversal
import all Linear.ProjectiveAffineLinearSection
import all Linear.ProjectiveAffineLinearSectionComparison
import all Linear.ProjectiveAffinePoint
import all Linear.ProjectiveAffinePointData
import all Linear.ProjectiveAffinePrime
import all Linear.ProjectiveAffineSmoothLocus
import all Linear.ProjectiveAffineSmoothPoint
import all Linear.ProjectiveAffineVariety
import all Linear.ProjectiveAmbientAtPoint
import all Linear.ProjectiveAmbientOpenComparison
import all Linear.ProjectiveAmbientUnramifiedPoint
import all Linear.ProjectiveChart
import all Linear.ProjectiveChartFractionField
import all Linear.ProjectiveChartGenericMap
import all Linear.ProjectiveChartGoodPoint
import all Linear.ProjectiveChartHilbertKrullDimension
import all Linear.ProjectiveChartMapCoordinates
import all Linear.ProjectiveChartOpenMap
import all Linear.ProjectiveChartPointEvaluation
import all Linear.ProjectiveChartSmoothUnramified
import all Linear.ProjectiveChartUnramifiedOpen
import all Linear.ProjectiveCommonChart
import all Linear.ProjectiveConeChartEvaluation
import all Linear.ProjectiveConeChartOpenIntersection
import all Linear.ProjectiveConeCoordinateTranscendental
import all Linear.ProjectiveConeFinite
import all Linear.ProjectiveConeGoodTargetPoint
import all Linear.ProjectiveConeHilbertKrullDimension
import all Linear.ProjectiveConeRatioRatFunc
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.PolynomialPointEvaluation","Linear.PolynomialProjectionFiberQuotient","Linear.PolynomialRecentering","Linear.PolynomialRectangleDimension","Linear.PolynomialReducedPointCount","Linear.PolynomialRegular","Linear.PolynomialSmoothCoordinates","Linear.PolynomialSmoothReduction","Linear.PolynomialSocle","Linear.PolynomialTotalDegreeHilbert","Linear.PowerSeriesAugmentation","Linear.PowerSeriesCentering","Linear.PowerSeriesCoefficients","Linear.PowerSeriesCoordinateChart","Linear.PowerSeriesDerivative","Linear.PowerSeriesDiagonal","Linear.PowerSeriesFlatten","Linear.PowerSeriesFlattenDerivative","Linear.PowerSeriesRegular","Linear.PowerSeriesSocle","Linear.PowerSeriesSpecialization","Linear.PowerSeriesTranslation","Linear.Primitive","Linear.Projective","Linear.ProjectiveAffineFiberClosedPullback","Linear.ProjectiveAffineFiberFinite","Linear.ProjectiveAffineFiberMap","Linear.ProjectiveAffineFiberPointEquiv","Linear.ProjectiveAffineFiberReduced","Linear.ProjectiveAffineFiberUnit","Linear.ProjectiveAffineFiberUniversal","Linear.ProjectiveAffineLinearSection","Linear.ProjectiveAffineLinearSectionComparison","Linear.ProjectiveAffinePoint","Linear.ProjectiveAffinePointData","Linear.ProjectiveAffinePrime","Linear.ProjectiveAffineSmoothLocus","Linear.ProjectiveAffineSmoothPoint","Linear.ProjectiveAffineVariety","Linear.ProjectiveAmbientAtPoint","Linear.ProjectiveAmbientOpenComparison","Linear.ProjectiveAmbientUnramifiedPoint","Linear.ProjectiveChart","Linear.ProjectiveChartFractionField","Linear.ProjectiveChartGenericMap","Linear.ProjectiveChartGoodPoint","Linear.ProjectiveChartHilbertKrullDimension","Linear.ProjectiveChartMapCoordinates","Linear.ProjectiveChartOpenMap","Linear.ProjectiveChartPointEvaluation","Linear.ProjectiveChartSmoothUnramified","Linear.ProjectiveChartUnramifiedOpen","Linear.ProjectiveCommonChart","Linear.ProjectiveConeChartEvaluation","Linear.ProjectiveConeChartOpenIntersection","Linear.ProjectiveConeCoordinateTranscendental","Linear.ProjectiveConeFinite","Linear.ProjectiveConeGoodTargetPoint","Linear.ProjectiveConeHilbertKrullDimension","Linear.ProjectiveConeRatioRatFunc"]
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
