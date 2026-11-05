module
import all Linear.NativeComplementaryMonomialCechNaturality
import all Linear.NativeComplementaryPolynomialSheaf
import all Linear.NativeCoordinatePolynomialMultiplication
import all Linear.NativeCoordinateRatio
import all Linear.NativeDualDegreeZeroSpanValues
import all Linear.NativeDualHomogeneousFractionValues
import all Linear.NativeDualLocalizationFractionValues
import all Linear.NativeFiniteGradedChartSectionsSurjective
import all Linear.NativeFiniteGradedIndependentCechSections
import all Linear.NativeFiniteGradedSourceAmbientCechFaces
import all Linear.NativeFiniteGradedSourceAmbientCechObjects
import all Linear.NativeFiniteGradedSourceAmbientCechSections
import all Linear.NativeFiniteGradedSourceAmbientOrderedCech
import all Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
import all Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective
import all Linear.NativeFiniteTwistTopDuality
import all Linear.NativeFormalFreeValueHom
import all Linear.NativeFreeCoproductHomAddEquiv
import all Linear.NativeGradedBaseSourceChart
import all Linear.NativeGradedBaseSourceMap
import all Linear.NativeGradedBaseSourceScalar
import all Linear.NativeGradedChartSingleFraction
import all Linear.NativeGradedKernelTopCechCokernel
import all Linear.NativeGradedKernelTopCechCokernelIso
import all Linear.NativeGradedModuleAway
import all Linear.NativeGradedModuleOverlapDegree
import all Linear.NativeGradedPolynomialDegreeTransport
import all Linear.NativeGradedPolynomialEntry
import all Linear.NativeGradedPresentationMapLiftSquare
import all Linear.NativeGradedPresentationTopCechCokernel
import all Linear.NativeGradedPresentationTopCechQuotient
import all Linear.NativeGradedWeightedBaseSourceMap
import all Linear.NativeGradedWeightedBaseSourceScalar
import all Linear.NativeGradedWeightedOverlap
import all Linear.NativeHomogeneousAwayTwist
import all Linear.NativeHomogeneousAwayTwistFraction
import all Linear.NativeHomogeneousGlobalSection
import all Linear.NativeHomogeneousLaurentMonomial
import all Linear.NativeHomogeneousLaurentSection
import all Linear.NativeHomogeneousMultiplicationFrame
import all Linear.NativeHomogeneousSectionFrame
import all Linear.NativeIndependentNormalizationActualHComparison
import all Linear.NativeIndependentNormalizationActualHFactorization
import all Linear.NativeIndependentNormalizationActualHScalar
import all Linear.NativeIndependentNormalizationHFactorization
import all Linear.NativeIndependentNormalizationModuleHComparison
import all Linear.NativeIndependentNormalizationModuleHLinearComparison
import all Linear.NativeIndependentNormalizationModuleHPointwiseScalar
import all Linear.NativeIndependentNormalizationModuleHScalar
import all Linear.NativeIndependentSourceAmbientCechBaseScalar
import all Linear.NativeIndependentSourceAmbientCechFaces
import all Linear.NativeIndependentSourceAmbientCechIntersectionScalar
import all Linear.NativeIndependentSourceAmbientCechObjects
import all Linear.NativeIndependentSourceAmbientCechProductScalar
import all Linear.NativeIndependentSourceAmbientCechSectionScalar
import all Linear.NativeIndependentSourceAmbientCechSections
import all Linear.NativeIndependentSourceAmbientOrderedCech
import all Linear.NativeIndependentSourceAmbientOrderedCechScalar
import all Linear.NativeIndependentSourceAmbientOrderedTwistCech
import all Linear.NativeIndependentSourceAmbientOrderedTwistCechScalar
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeComplementaryMonomialCechNaturality","Linear.NativeComplementaryPolynomialSheaf","Linear.NativeCoordinatePolynomialMultiplication","Linear.NativeCoordinateRatio","Linear.NativeDualDegreeZeroSpanValues","Linear.NativeDualHomogeneousFractionValues","Linear.NativeDualLocalizationFractionValues","Linear.NativeFiniteGradedChartSectionsSurjective","Linear.NativeFiniteGradedIndependentCechSections","Linear.NativeFiniteGradedSourceAmbientCechFaces","Linear.NativeFiniteGradedSourceAmbientCechObjects","Linear.NativeFiniteGradedSourceAmbientCechSections","Linear.NativeFiniteGradedSourceAmbientOrderedCech","Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech","Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective","Linear.NativeFiniteTwistTopDuality","Linear.NativeFormalFreeValueHom","Linear.NativeFreeCoproductHomAddEquiv","Linear.NativeGradedBaseSourceChart","Linear.NativeGradedBaseSourceMap","Linear.NativeGradedBaseSourceScalar","Linear.NativeGradedChartSingleFraction","Linear.NativeGradedKernelTopCechCokernel","Linear.NativeGradedKernelTopCechCokernelIso","Linear.NativeGradedModuleAway","Linear.NativeGradedModuleOverlapDegree","Linear.NativeGradedPolynomialDegreeTransport","Linear.NativeGradedPolynomialEntry","Linear.NativeGradedPresentationMapLiftSquare","Linear.NativeGradedPresentationTopCechCokernel","Linear.NativeGradedPresentationTopCechQuotient","Linear.NativeGradedWeightedBaseSourceMap","Linear.NativeGradedWeightedBaseSourceScalar","Linear.NativeGradedWeightedOverlap","Linear.NativeHomogeneousAwayTwist","Linear.NativeHomogeneousAwayTwistFraction","Linear.NativeHomogeneousGlobalSection","Linear.NativeHomogeneousLaurentMonomial","Linear.NativeHomogeneousLaurentSection","Linear.NativeHomogeneousMultiplicationFrame","Linear.NativeHomogeneousSectionFrame","Linear.NativeIndependentNormalizationActualHComparison","Linear.NativeIndependentNormalizationActualHFactorization","Linear.NativeIndependentNormalizationActualHScalar","Linear.NativeIndependentNormalizationHFactorization","Linear.NativeIndependentNormalizationModuleHComparison","Linear.NativeIndependentNormalizationModuleHLinearComparison","Linear.NativeIndependentNormalizationModuleHPointwiseScalar","Linear.NativeIndependentNormalizationModuleHScalar","Linear.NativeIndependentSourceAmbientCechBaseScalar","Linear.NativeIndependentSourceAmbientCechFaces","Linear.NativeIndependentSourceAmbientCechIntersectionScalar","Linear.NativeIndependentSourceAmbientCechObjects","Linear.NativeIndependentSourceAmbientCechProductScalar","Linear.NativeIndependentSourceAmbientCechSectionScalar","Linear.NativeIndependentSourceAmbientCechSections","Linear.NativeIndependentSourceAmbientOrderedCech","Linear.NativeIndependentSourceAmbientOrderedCechScalar","Linear.NativeIndependentSourceAmbientOrderedTwistCech","Linear.NativeIndependentSourceAmbientOrderedTwistCechScalar"]
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
