module
import all Linear.AddMonoidAlgebraLocalization
import all Linear.AwayCongr
import all Linear.CechSupportContraction
import all Linear.CechTuplePermutations
import all Linear.FiniteBiproductDualCoordinates
import all Linear.FiniteBiproductMatrixDuality
import all Linear.FinitePiDualEquiv
import all Linear.FinitePiDualNaturality
import all Linear.LaurentExponentLocalization
import all Linear.LaurentMonomialBasis
import all Linear.ModuleBaseCechBasic
import all Linear.ModuleBaseCechFactors
import all Linear.ModuleFormalCoproductAdditive
import all Linear.ModuleOrderedBaseCech
import all Linear.OrderedCechFullSupport
import all Linear.OrderedCechSupportAlternating
import all Linear.OrderedCechSupportContraction
import all Linear.ProjectiveCanonicalCoefficientEquiv
import all Linear.ProjectiveCanonicalResidue
import all Linear.ProjectiveCanonicalResidueKernel
import all Linear.ProjectiveCechLaurentRestriction
import all Linear.ProjectiveCechLaurentSections
import all Linear.ProjectiveCoordinateOpens
import all Linear.ProjectiveGeneralResidueCoordinates
import all Linear.ProjectiveGeneralResidueDuality
import all Linear.ProjectiveGeneralResidueSurjective
import all Linear.ProjectiveHomogeneousBasisProduct
import all Linear.ProjectiveHomogeneousCoefficientEquiv
import all Linear.ProjectiveHomogeneousCoefficientTransport
import all Linear.ProjectiveHomogeneousMultiplication
import all Linear.ProjectiveLaurentCardinality
import all Linear.ProjectiveLaurentCechWeights
import all Linear.ProjectiveLaurentGeneralTopBoundary
import all Linear.ProjectiveLaurentInitialChartMap
import all Linear.ProjectiveLaurentInitialExponent
import all Linear.ProjectiveLaurentInitialGenerators
import all Linear.ProjectiveLaurentInitialRestriction
import all Linear.ProjectiveLaurentNoninitialRestriction
import all Linear.ProjectiveLaurentTopWeight
import all Linear.ProjectiveLaurentWeight
import all Linear.ProjectiveLaurentWeightAssembly
import all Linear.ProjectiveLaurentWeightComponents
import all Linear.ProjectiveNegativeWeightComplement
import all Linear.ProjectiveSpaceChart
import all Linear.ProjectiveStandardIntersectionRing
import all Linear.ProjStructureSectionSquare
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
  if count <= 27 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
