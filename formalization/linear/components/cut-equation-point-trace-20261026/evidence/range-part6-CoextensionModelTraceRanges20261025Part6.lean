module
import all Linear.NativeIntegerFreeFamilyHomDuality
import all Linear.NativeIntegerFreeHomDuality
import all Linear.NativeIntegerFreeRelationMatrixDuality
import all Linear.NativeIntegerFreeTwistMapNaturality
import all Linear.NativeIntegerFreeTwistRegrading
import all Linear.NativeIntegerMixedPresentationCechHomDuality
import all Linear.NativeIntegerMixedPresentationTopCokernel
import all Linear.NativeIntegerPrimeTwist
import all Linear.NativeIntegerRelationEntryDuality
import all Linear.NativeIntegerRelationHighEntryTransport
import all Linear.NativeIntegerRelationLowEntryDuality
import all Linear.NativeIntegerTwistBaseSections
import all Linear.NativeIntegerTwistChartSingleFraction
import all Linear.NativeIntegerTwistDegreeTransport
import all Linear.NativeIntegerTwistFrameTransition
import all Linear.NativeIntegerTwistScalarCommute
import all Linear.NativeIntegerTwistSectionFrames
import all Linear.NativeIntegerTwistedFreeFamilyHomDuality
import all Linear.NativeIntegerTwistedFreeRelationDuality
import all Linear.NativeIntegerTwistedPresentationCechHomDuality
import all Linear.NativeIntegerTwistedPresentationMapDuality
import all Linear.NativeIntegerTwistedPresentationQuotientDuality
import all Linear.NativeIntegerTwistedPresentationQuotientEpi
import all Linear.NativeLocalizationScalarComparison
import all Linear.NativeLocalizedUpperAlgebra
import all Linear.NativeMonomialCechNaturality
import all Linear.NativeMonomialMultiplicationLaurent
import all Linear.NativeMonomialTopDualityNaturality
import all Linear.NativeNormalizationActualHKLinearIso
import all Linear.NativeNormalizationFullChartComparison
import all Linear.NativePolynomialCechFactorMap
import all Linear.NativePolynomialComplexFamily
import all Linear.NativePolynomialEntryValues
import all Linear.NativePolynomialMultiplicationAdditivity
import all Linear.NativePolynomialPresentationWeights
import all Linear.NativePolynomialTopDualityNaturality
import all Linear.NativeProjActualHCoefficientNaturality
import all Linear.NativeProjActualHComparison
import all Linear.NativeProjectiveAboveCanonicalCechVanishing
import all Linear.NativeProjectiveCechAffineIntersections
import all Linear.NativeProjectiveChart
import all Linear.NativeProjectiveChartInjectiveAll
import all Linear.NativeProjectiveChartRefinement
import all Linear.NativeProjectiveChartSections
import all Linear.NativeProjectiveChartSectionsInjective
import all Linear.NativeProjectiveChartSectionsOverlap
import all Linear.NativeProjectiveDegreeOneCover
import all Linear.NativeProjectiveDegreeZeroComposition
import all Linear.NativeProjectiveDegreeZeroEpi
import all Linear.NativeProjectiveDegreeZeroIdentities
import all Linear.NativeProjectiveDegreeZeroMap
import all Linear.NativeProjectiveExactFinitePresentation
import all Linear.NativeProjectiveFiniteFreeEpi
import all Linear.NativeProjectiveFiniteGradedChartPresentation
import all Linear.NativeProjectiveFiniteGradedFiniteChart
import all Linear.NativeProjectiveFiniteGradedFinitePresentation
import all Linear.NativeProjectiveFiniteGradedQuasicoherent
import all Linear.NativeProjectiveGeneralTopDuality
import all Linear.NativeProjectiveGradedKernelCech
import all Linear.NativeProjectiveHomogeneousSMul
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeIntegerFreeFamilyHomDuality","Linear.NativeIntegerFreeHomDuality","Linear.NativeIntegerFreeRelationMatrixDuality","Linear.NativeIntegerFreeTwistMapNaturality","Linear.NativeIntegerFreeTwistRegrading","Linear.NativeIntegerMixedPresentationCechHomDuality","Linear.NativeIntegerMixedPresentationTopCokernel","Linear.NativeIntegerPrimeTwist","Linear.NativeIntegerRelationEntryDuality","Linear.NativeIntegerRelationHighEntryTransport","Linear.NativeIntegerRelationLowEntryDuality","Linear.NativeIntegerTwistBaseSections","Linear.NativeIntegerTwistChartSingleFraction","Linear.NativeIntegerTwistDegreeTransport","Linear.NativeIntegerTwistFrameTransition","Linear.NativeIntegerTwistScalarCommute","Linear.NativeIntegerTwistSectionFrames","Linear.NativeIntegerTwistedFreeFamilyHomDuality","Linear.NativeIntegerTwistedFreeRelationDuality","Linear.NativeIntegerTwistedPresentationCechHomDuality","Linear.NativeIntegerTwistedPresentationMapDuality","Linear.NativeIntegerTwistedPresentationQuotientDuality","Linear.NativeIntegerTwistedPresentationQuotientEpi","Linear.NativeLocalizationScalarComparison","Linear.NativeLocalizedUpperAlgebra","Linear.NativeMonomialCechNaturality","Linear.NativeMonomialMultiplicationLaurent","Linear.NativeMonomialTopDualityNaturality","Linear.NativeNormalizationActualHKLinearIso","Linear.NativeNormalizationFullChartComparison","Linear.NativePolynomialCechFactorMap","Linear.NativePolynomialComplexFamily","Linear.NativePolynomialEntryValues","Linear.NativePolynomialMultiplicationAdditivity","Linear.NativePolynomialPresentationWeights","Linear.NativePolynomialTopDualityNaturality","Linear.NativeProjActualHCoefficientNaturality","Linear.NativeProjActualHComparison","Linear.NativeProjectiveAboveCanonicalCechVanishing","Linear.NativeProjectiveCechAffineIntersections","Linear.NativeProjectiveChart","Linear.NativeProjectiveChartInjectiveAll","Linear.NativeProjectiveChartRefinement","Linear.NativeProjectiveChartSections","Linear.NativeProjectiveChartSectionsInjective","Linear.NativeProjectiveChartSectionsOverlap","Linear.NativeProjectiveDegreeOneCover","Linear.NativeProjectiveDegreeZeroComposition","Linear.NativeProjectiveDegreeZeroEpi","Linear.NativeProjectiveDegreeZeroIdentities","Linear.NativeProjectiveDegreeZeroMap","Linear.NativeProjectiveExactFinitePresentation","Linear.NativeProjectiveFiniteFreeEpi","Linear.NativeProjectiveFiniteGradedChartPresentation","Linear.NativeProjectiveFiniteGradedFiniteChart","Linear.NativeProjectiveFiniteGradedFinitePresentation","Linear.NativeProjectiveFiniteGradedQuasicoherent","Linear.NativeProjectiveGeneralTopDuality","Linear.NativeProjectiveGradedKernelCech","Linear.NativeProjectiveHomogeneousSMul"]
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
