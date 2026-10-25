module
import all Linear.LinearNormalizationBasePoint
import all Linear.LinearProjectionFiberPointEquiv
import all Linear.LinearProjectionFilteredGrowth
import all Linear.LinearProjectionGradedControl
import all Linear.LinearProjectionSectionAvoidance
import all Linear.LocalComplexExactReflection
import all Linear.LocalExactReflection
import all Linear.LocalFiber
import all Linear.LocalFiberJacobian
import all Linear.LocalGeneratorsEquiv
import all Linear.LocalMapEquivComparison
import all Linear.LocalPullbackEssentialFiniteType
import all Linear.LocalPullbackGenerators
import all Linear.LocalQuotientMaximalIdeal
import all Linear.LocalQuotientPullback
import all Linear.LocalResidueEvaluation
import all Linear.LocalizedAnnihilator
import all Linear.LocalizedDifferentialBasis
import all Linear.LocalizedDifferentialRank
import all Linear.MappedChainCokernelPresentation
import all Linear.MappedChainPresentationData
import all Linear.MappedCokernelProjectionInvariant
import all Linear.MatrixControlledPolynomialSpan
import all Linear.NativeCoordinateRatio
import all Linear.NativeExtUniverseTransport
import all Linear.NativeGlobalKoszulAffineCounit
import all Linear.NativeGlobalKoszulAffineStandard
import all Linear.NativeGlobalKoszulChartSectionComplex
import all Linear.NativeGlobalKoszulDehomogenizedDifferential
import all Linear.NativeGlobalKoszulFrameEntries
import all Linear.NativeGlobalKoszulQuasicoherent
import all Linear.NativeGlobalKoszulSectionMatrix
import all Linear.NativeGlobalKoszulSpecDifferential
import all Linear.NativeGlobalKoszulSpecSectionComplex
import all Linear.NativeHomogeneousGlobalSection
import all Linear.NativeHomogeneousIntegerFrameMultiply
import all Linear.NativeHomogeneousSectionFrame
import all Linear.NativeIntegerFreeSpecChartFrames
import all Linear.NativeIntegerFreeTwistRegrading
import all Linear.NativeIntegerPrimeTwist
import all Linear.NativeIntegerShiftedFreeBicone
import all Linear.NativeIntegerShiftedFreeCoordinateMaps
import all Linear.NativeIntegerShiftedFreeSectionFrames
import all Linear.NativeIntegerTwistDegreeTransport
import all Linear.NativeIntegerTwistInternalExtVanishing
import all Linear.NativeIntegerTwistScalarCommute
import all Linear.NativeIntegerTwistSectionFrames
import all Linear.NativeIntegerTwistWholeChartFrame
import all Linear.NativeKoszulChartCoefficientSpec
import all Linear.NativeKoszulCoefficientUnit
import all Linear.NativeKoszulCokernelChartFromPresentation
import all Linear.NativeKoszulFiniteTopTerm
import all Linear.NativeKoszulGlobalCokernelChartPushforward
import all Linear.NativeKoszulGlobalExactFromChart
import all Linear.NativeKoszulMappedChartBoundary
import all Linear.NativeKoszulMappedChartComplexIdentity
import all Linear.NativeKoszulMappedPresentationData
import all Linear.NativeKoszulOffCutActualStalkExact
import all Linear.NativeKoszulOffCutAllDegrees
import all Linear.NativeKoszulOffCutCokernelZero
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.LinearNormalizationBasePoint","Linear.LinearProjectionFiberPointEquiv","Linear.LinearProjectionFilteredGrowth","Linear.LinearProjectionGradedControl","Linear.LinearProjectionSectionAvoidance","Linear.LocalComplexExactReflection","Linear.LocalExactReflection","Linear.LocalFiber","Linear.LocalFiberJacobian","Linear.LocalGeneratorsEquiv","Linear.LocalMapEquivComparison","Linear.LocalPullbackEssentialFiniteType","Linear.LocalPullbackGenerators","Linear.LocalQuotientMaximalIdeal","Linear.LocalQuotientPullback","Linear.LocalResidueEvaluation","Linear.LocalizedAnnihilator","Linear.LocalizedDifferentialBasis","Linear.LocalizedDifferentialRank","Linear.MappedChainCokernelPresentation","Linear.MappedChainPresentationData","Linear.MappedCokernelProjectionInvariant","Linear.MatrixControlledPolynomialSpan","Linear.NativeCoordinateRatio","Linear.NativeExtUniverseTransport","Linear.NativeGlobalKoszulAffineCounit","Linear.NativeGlobalKoszulAffineStandard","Linear.NativeGlobalKoszulChartSectionComplex","Linear.NativeGlobalKoszulDehomogenizedDifferential","Linear.NativeGlobalKoszulFrameEntries","Linear.NativeGlobalKoszulQuasicoherent","Linear.NativeGlobalKoszulSectionMatrix","Linear.NativeGlobalKoszulSpecDifferential","Linear.NativeGlobalKoszulSpecSectionComplex","Linear.NativeHomogeneousGlobalSection","Linear.NativeHomogeneousIntegerFrameMultiply","Linear.NativeHomogeneousSectionFrame","Linear.NativeIntegerFreeSpecChartFrames","Linear.NativeIntegerFreeTwistRegrading","Linear.NativeIntegerPrimeTwist","Linear.NativeIntegerShiftedFreeBicone","Linear.NativeIntegerShiftedFreeCoordinateMaps","Linear.NativeIntegerShiftedFreeSectionFrames","Linear.NativeIntegerTwistDegreeTransport","Linear.NativeIntegerTwistInternalExtVanishing","Linear.NativeIntegerTwistScalarCommute","Linear.NativeIntegerTwistSectionFrames","Linear.NativeIntegerTwistWholeChartFrame","Linear.NativeKoszulChartCoefficientSpec","Linear.NativeKoszulCoefficientUnit","Linear.NativeKoszulCokernelChartFromPresentation","Linear.NativeKoszulFiniteTopTerm","Linear.NativeKoszulGlobalCokernelChartPushforward","Linear.NativeKoszulGlobalExactFromChart","Linear.NativeKoszulMappedChartBoundary","Linear.NativeKoszulMappedChartComplexIdentity","Linear.NativeKoszulMappedPresentationData","Linear.NativeKoszulOffCutActualStalkExact","Linear.NativeKoszulOffCutAllDegrees","Linear.NativeKoszulOffCutCokernelZero"]
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
