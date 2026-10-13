module
import all Linear.AddMonoidAlgebraLocalization
import all Linear.AwayCongr
import all Linear.CechSupportContraction
import all Linear.CechTuplePermutations
import all Linear.GradedIntegerProjection
import all Linear.GradedModuleProjection
import all Linear.LaurentExponentLocalization
import all Linear.LaurentMonomialBasis
import all Linear.ModuleBaseCechBasic
import all Linear.ModuleBaseCechFactors
import all Linear.ModuleCechScHomologyNaturality
import all Linear.ModuleFormalCoproductAdditive
import all Linear.ModuleOrderedBaseCech
import all Linear.ModuleOrderedBaseCechFunctor
import all Linear.ModuleOrderedCechAugmentation
import all Linear.ModuleShortComplexTopQuotientNaturality
import all Linear.ModuleTopHomologyScalar
import all Linear.NativeCechComplexDegreeTransport
import all Linear.NativeComplementaryMonomialCechNaturality
import all Linear.NativeCoordinatePolynomialMultiplication
import all Linear.NativeCoordinateRatio
import all Linear.NativeHomogeneousGlobalSection
import all Linear.NativeHomogeneousLaurentMonomial
import all Linear.NativeHomogeneousLaurentSection
import all Linear.NativeHomogeneousMultiplicationFrame
import all Linear.NativeHomogeneousSectionFrame
import all Linear.NativeIntegerPrimeTwist
import all Linear.NativeIntegerTwistBaseSections
import all Linear.NativeIntegerTwistFrameTransition
import all Linear.NativeIntegerTwistScalarCommute
import all Linear.NativeIntegerTwistSectionFrames
import all Linear.NativeMonomialCechNaturality
import all Linear.NativeMonomialMultiplicationLaurent
import all Linear.NativeMonomialTopDualityNaturality
import all Linear.NativePolynomialCechFactorMap
import all Linear.NativePolynomialComplexFamily
import all Linear.NativePolynomialMultiplicationAdditivity
import all Linear.NativePolynomialTopDualityNaturality
import all Linear.NativeProjectiveGeneralTopDuality
import all Linear.NativeProjectiveHomogeneousSMul
import all Linear.NativeProjectiveIntegerTwistChartFree
import all Linear.NativeProjectiveLaurentComplex
import all Linear.NativeProjectiveLaurentFactors
import all Linear.NativeProjectiveLaurentInitial
import all Linear.NativeProjectiveLaurentNoninitial
import all Linear.NativeProjectiveLaurentTransition
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
import all Linear.NativeProjectiveTwistChartFree
import all Linear.NativeProjectiveTwistFraction
import all Linear.NativeProjectiveTwistSectionEquiv
import all Linear.NativeProjectiveTwistSheafOverIso
import all Linear.NativeScaledMonomialCechNaturality
import all Linear.NativeScaledMonomialMultiplicationLaurent
import all Linear.NativeScaledMonomialTopDuality
import all Linear.NativeStructureModuleFraction
import all Linear.NativeStructureModuleSections
import all Linear.NativeStructureModuleSheaf
import all Linear.OrderedCechFullSupport
import all Linear.OrderedCechSupportAlternating
import all Linear.OrderedCechSupportContraction
import all Linear.OrderedCechSupportZero
import all Linear.ProjStructureSectionSquare
import all Linear.ProjectiveCanonicalResidue
import all Linear.ProjectiveCanonicalResidueKernel
import all Linear.ProjectiveCechLaurentRestriction
import all Linear.ProjectiveCechLaurentSections
import all Linear.ProjectiveComplementaryCechDifferential
import all Linear.ProjectiveComplementaryCechShift
import all Linear.ProjectiveCoordinateOpens
import all Linear.ProjectiveGeneralResidueCoordinates
import all Linear.ProjectiveGeneralResidueDuality
import all Linear.ProjectiveGeneralResidueSurjective
import all Linear.ProjectiveHomogeneousBasisProduct
import all Linear.ProjectiveHomogeneousCoefficientTransport
import all Linear.ProjectiveHomogeneousMonomialLaurent
import all Linear.ProjectiveHomogeneousMultiplication
import all Linear.ProjectiveHomogeneousMultiplicationFamily
import all Linear.ProjectiveLaurentCardinality
import all Linear.ProjectiveLaurentCechScalarShift
import all Linear.ProjectiveLaurentCechShift
import all Linear.ProjectiveLaurentCechShiftCoefficients
import all Linear.ProjectiveLaurentCechWeights
import all Linear.ProjectiveLaurentDegreeTransport
import all Linear.ProjectiveLaurentGeneralTopBoundary
import all Linear.ProjectiveLaurentInitialChartMap
import all Linear.ProjectiveLaurentInitialExponent
import all Linear.ProjectiveLaurentInitialGenerators
import all Linear.ProjectiveLaurentInitialRestriction
import all Linear.ProjectiveLaurentNatExponent
import all Linear.ProjectiveLaurentNoninitialRestriction
import all Linear.ProjectiveLaurentReindexShift
import all Linear.ProjectiveLaurentScaledSectionShift
import all Linear.ProjectiveLaurentSectionShift
import all Linear.ProjectiveLaurentShiftCoefficients
import all Linear.ProjectiveLaurentShiftComplex
import all Linear.ProjectiveLaurentShiftLinear
import all Linear.ProjectiveLaurentShiftProduct
import all Linear.ProjectiveLaurentTopWeight
import all Linear.ProjectiveLaurentWeight
import all Linear.ProjectiveLaurentWeightAssembly
import all Linear.ProjectiveLaurentWeightComponents
import all Linear.ProjectiveLaurentWeightShift
import all Linear.ProjectiveLaurentZeroCycle
import all Linear.ProjectiveMonomialDualTranspose
import all Linear.ProjectiveMonomialFullHomologyNaturality
import all Linear.ProjectiveMonomialResidueDuality
import all Linear.ProjectiveMonomialResidueNaturality
import all Linear.ProjectiveMonomialTopHomologyNaturality
import all Linear.ProjectiveMonomialTopQuotientNaturality
import all Linear.ProjectiveNegativeWeightComplement
import all Linear.ProjectivePositiveMonomialWeight
import all Linear.ProjectiveSpaceChart
import all Linear.ProjectiveStandardIntersectionRing
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
  if count <= 29 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
