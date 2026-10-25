module
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
import all Linear.ProjBasicOpenBaseScalar
import all Linear.ProjStructureSectionRestriction
import all Linear.ProjStructureSectionScalarValue
import all Linear.ProjStructureSectionSquare
import all Linear.Projective
import all Linear.ProjectiveAffinePoint
import all Linear.ProjectiveAffinePrime
import all Linear.ProjectiveAffineVariety
import all Linear.ProjectiveCanonicalCoefficientEquiv
import all Linear.ProjectiveCanonicalDualCoefficientEquiv
import all Linear.ProjectiveCanonicalResidue
import all Linear.ProjectiveCanonicalResidueKernel
import all Linear.ProjectiveCechLaurentRestriction
import all Linear.ProjectiveCechLaurentSections
import all Linear.ProjectiveChartFractionField
import all Linear.ProjectiveComplementaryCechDifferential
import all Linear.ProjectiveComplementaryCechShift
import all Linear.ProjectiveConeSurjectivity
import all Linear.ProjectiveCoordinateDomainMap
import all Linear.ProjectiveCoordinateFractionMap
import all Linear.ProjectiveCoordinateOpens
import all Linear.ProjectiveCoordinateRatioMap
import all Linear.ProjectiveDualCoefficientRestriction
import all Linear.ProjectiveGeneralResidueCoordinates
import all Linear.ProjectiveGeneralResidueDuality
import all Linear.ProjectiveGeneralResidueSurjective
import all Linear.ProjectiveGradedDualCoefficientEquiv
import all Linear.ProjectiveHomogeneousBasisProduct
import all Linear.ProjectiveHomogeneousCoefficientEquiv
import all Linear.ProjectiveHomogeneousCoefficientTransport
import all Linear.ProjectiveHomogeneousDualCoefficientEquiv
import all Linear.ProjectiveHomogeneousMonomialLaurent
import all Linear.ProjectiveHomogeneousMultiplication
import all Linear.ProjectiveHomogeneousMultiplicationFamily
import all Linear.ProjectiveIdealInvariance
import all Linear.ProjectiveIntegerHighWeightTransport
import all Linear.ProjectiveIntegerHomogeneousPieces
import all Linear.ProjectiveLaurentAboveCanonicalBoundary
import all Linear.ProjectiveLaurentCardinality
import all Linear.ProjectiveLaurentCechScalarShift
import all Linear.ProjectiveLaurentCechShift
import all Linear.ProjectiveLaurentCechShiftCoefficients
import all Linear.ProjectiveLaurentCechWeights
import all Linear.ProjectiveLaurentDegreeThreshold
import all Linear.ProjectiveLaurentDegreeTransport
import all Linear.ProjectiveLaurentGeneralTopBoundary
import all Linear.ProjectiveLaurentInitialChartMap
import all Linear.ProjectiveLaurentInitialExponent
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.PowerSeriesCentering","Linear.PowerSeriesCoefficients","Linear.PowerSeriesCoordinateChart","Linear.PowerSeriesDerivative","Linear.PowerSeriesDiagonal","Linear.PowerSeriesFlatten","Linear.PowerSeriesFlattenDerivative","Linear.PowerSeriesRegular","Linear.PowerSeriesSocle","Linear.PowerSeriesSpecialization","Linear.PowerSeriesTranslation","Linear.Primitive","Linear.ProjBasicOpenBaseScalar","Linear.ProjStructureSectionRestriction","Linear.ProjStructureSectionScalarValue","Linear.ProjStructureSectionSquare","Linear.Projective","Linear.ProjectiveAffinePoint","Linear.ProjectiveAffinePrime","Linear.ProjectiveAffineVariety","Linear.ProjectiveCanonicalCoefficientEquiv","Linear.ProjectiveCanonicalDualCoefficientEquiv","Linear.ProjectiveCanonicalResidue","Linear.ProjectiveCanonicalResidueKernel","Linear.ProjectiveCechLaurentRestriction","Linear.ProjectiveCechLaurentSections","Linear.ProjectiveChartFractionField","Linear.ProjectiveComplementaryCechDifferential","Linear.ProjectiveComplementaryCechShift","Linear.ProjectiveConeSurjectivity","Linear.ProjectiveCoordinateDomainMap","Linear.ProjectiveCoordinateFractionMap","Linear.ProjectiveCoordinateOpens","Linear.ProjectiveCoordinateRatioMap","Linear.ProjectiveDualCoefficientRestriction","Linear.ProjectiveGeneralResidueCoordinates","Linear.ProjectiveGeneralResidueDuality","Linear.ProjectiveGeneralResidueSurjective","Linear.ProjectiveGradedDualCoefficientEquiv","Linear.ProjectiveHomogeneousBasisProduct","Linear.ProjectiveHomogeneousCoefficientEquiv","Linear.ProjectiveHomogeneousCoefficientTransport","Linear.ProjectiveHomogeneousDualCoefficientEquiv","Linear.ProjectiveHomogeneousMonomialLaurent","Linear.ProjectiveHomogeneousMultiplication","Linear.ProjectiveHomogeneousMultiplicationFamily","Linear.ProjectiveIdealInvariance","Linear.ProjectiveIntegerHighWeightTransport","Linear.ProjectiveIntegerHomogeneousPieces","Linear.ProjectiveLaurentAboveCanonicalBoundary","Linear.ProjectiveLaurentCardinality","Linear.ProjectiveLaurentCechScalarShift","Linear.ProjectiveLaurentCechShift","Linear.ProjectiveLaurentCechShiftCoefficients","Linear.ProjectiveLaurentCechWeights","Linear.ProjectiveLaurentDegreeThreshold","Linear.ProjectiveLaurentDegreeTransport","Linear.ProjectiveLaurentGeneralTopBoundary","Linear.ProjectiveLaurentInitialChartMap","Linear.ProjectiveLaurentInitialExponent"]
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
