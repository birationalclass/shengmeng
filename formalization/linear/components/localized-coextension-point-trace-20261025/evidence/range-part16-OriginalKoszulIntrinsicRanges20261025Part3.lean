module
import all Linear.FirstJet
import all Linear.FirstJetNormalForm
import all Linear.FirstOrderLocalParameters
import all Linear.FirstSyzygy
import all Linear.FormalFirstOrder
import all Linear.FormalInverseJacobian
import all Linear.FractionFieldTranscendence
import all Linear.FractionModelAlgebraicOpen
import all Linear.FreeAwayFiberRank
import all Linear.GeneralLocalQuotientPullback
import all Linear.GenericFiberRankOpen
import all Linear.GenericFreeAway
import all Linear.GenericSmoothOpen
import all Linear.GenericSmoothUnramifiedOpen
import all Linear.GenericSpanDenominator
import all Linear.GenericUnramifiedOpen
import all Linear.GlobalDiagonalNormalization
import all Linear.GoodRationalPointForMap
import all Linear.GradedGenericHomogeneousBasis
import all Linear.GradedHilbertDegree
import all Linear.GradedHilbertSeriesRecurrence
import all Linear.GradedHilbertSerre
import all Linear.GradedIntegerProjection
import all Linear.GradedIntegerProjector
import all Linear.GradedModuleFiniteSupport
import all Linear.GradedModuleHomogeneousGenerators
import all Linear.GradedModuleProjection
import all Linear.GradedQuotientDecomposition
import all Linear.GradedScalarExactSequence
import all Linear.GradedScalarInductionModules
import all Linear.GradedSubalgebraDecomposition
import all Linear.GradedSubmoduleDecomposition
import all Linear.GradedSurjectiveNativeCharts
import all Linear.GradedSurjectiveProjClosed
import all Linear.HilbertFiniteInstances
import all Linear.HilbertLeadingCoeffCumulative
import all Linear.HomCocycleShiftedComposition
import all Linear.HomogeneousAdjoinGenerators
import all Linear.HomogeneousChartLift
import all Linear.HomogeneousCoordinateComponentProduct
import all Linear.HomogeneousCoordinateFiltration
import all Linear.HomogeneousCoordinateGrading
import all Linear.HomogeneousCoordinateHilbertPolynomial
import all Linear.HomogeneousCoordinateHilbertPositive
import all Linear.HomogeneousCoordinateHilbertSeries
import all Linear.HomogeneousCoordinatePieces
import all Linear.HomogeneousCumulativeHilbert
import all Linear.HomogeneousCutChartCoverage
import all Linear.HomogeneousKoszulCoordinateComplex
import all Linear.HomogeneousLinearElimination
import all Linear.HomogeneousLinearMonic
import all Linear.HomogeneousLinearNormalization
import all Linear.HomogeneousLocalization
import all Linear.HomogeneousMapFinite
import all Linear.HomogeneousPullbackComponents
import all Linear.HomogeneousQuotient
import all Linear.HomogeneousQuotientKoszulAffineCounit
import all Linear.HomogeneousQuotientKoszulAffineStandard
import all Linear.HomogeneousQuotientKoszulTermInternalExtVanishing
import all Linear.HomogeneousQuotientNativeChart
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.FirstJet","Linear.FirstJetNormalForm","Linear.FirstOrderLocalParameters","Linear.FirstSyzygy","Linear.FormalFirstOrder","Linear.FormalInverseJacobian","Linear.FractionFieldTranscendence","Linear.FractionModelAlgebraicOpen","Linear.FreeAwayFiberRank","Linear.GeneralLocalQuotientPullback","Linear.GenericFiberRankOpen","Linear.GenericFreeAway","Linear.GenericSmoothOpen","Linear.GenericSmoothUnramifiedOpen","Linear.GenericSpanDenominator","Linear.GenericUnramifiedOpen","Linear.GlobalDiagonalNormalization","Linear.GoodRationalPointForMap","Linear.GradedGenericHomogeneousBasis","Linear.GradedHilbertDegree","Linear.GradedHilbertSeriesRecurrence","Linear.GradedHilbertSerre","Linear.GradedIntegerProjection","Linear.GradedIntegerProjector","Linear.GradedModuleFiniteSupport","Linear.GradedModuleHomogeneousGenerators","Linear.GradedModuleProjection","Linear.GradedQuotientDecomposition","Linear.GradedScalarExactSequence","Linear.GradedScalarInductionModules","Linear.GradedSubalgebraDecomposition","Linear.GradedSubmoduleDecomposition","Linear.GradedSurjectiveNativeCharts","Linear.GradedSurjectiveProjClosed","Linear.HilbertFiniteInstances","Linear.HilbertLeadingCoeffCumulative","Linear.HomCocycleShiftedComposition","Linear.HomogeneousAdjoinGenerators","Linear.HomogeneousChartLift","Linear.HomogeneousCoordinateComponentProduct","Linear.HomogeneousCoordinateFiltration","Linear.HomogeneousCoordinateGrading","Linear.HomogeneousCoordinateHilbertPolynomial","Linear.HomogeneousCoordinateHilbertPositive","Linear.HomogeneousCoordinateHilbertSeries","Linear.HomogeneousCoordinatePieces","Linear.HomogeneousCumulativeHilbert","Linear.HomogeneousCutChartCoverage","Linear.HomogeneousKoszulCoordinateComplex","Linear.HomogeneousLinearElimination","Linear.HomogeneousLinearMonic","Linear.HomogeneousLinearNormalization","Linear.HomogeneousLocalization","Linear.HomogeneousMapFinite","Linear.HomogeneousPullbackComponents","Linear.HomogeneousQuotient","Linear.HomogeneousQuotientKoszulAffineCounit","Linear.HomogeneousQuotientKoszulAffineStandard","Linear.HomogeneousQuotientKoszulTermInternalExtVanishing","Linear.HomogeneousQuotientNativeChart"]
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
