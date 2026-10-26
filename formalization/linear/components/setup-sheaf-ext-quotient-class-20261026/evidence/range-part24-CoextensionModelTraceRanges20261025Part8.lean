module
import all Linear.NativeSpecifiedNormalizationTopDualityKForget
import all Linear.NativeSpecifiedNormalizationTopDualityKLinearIso
import all Linear.NativeSpecifiedNormalizationTopDualityScalar
import all Linear.NativeSpecifiedNormalizationTopPairing
import all Linear.NativeStructureModuleFraction
import all Linear.NativeStructureModuleSections
import all Linear.NativeStructureModuleSheaf
import all Linear.NativeTwistRegradingMapNaturality
import all Linear.NativeWeightedAffineSectionsFunctionSurjective
import all Linear.NativeWeightedProjOpen
import all Linear.NativeWeightedSourceAmbientSectionEquiv
import all Linear.NativeWeightedSourceAmbientSectionNamedOverlap
import all Linear.NativeWeightedSourceAmbientSectionScalar
import all Linear.NativeWeightedSpecSectionFunctionScalar
import all Linear.NilpotentEvaluation
import all Linear.NilpotentEvaluationUnique
import all Linear.NilpotentRegular
import all Linear.NoetherianAffineActualCohomology
import all Linear.NoetherianAffineOpenActualCohomology
import all Linear.NoetherianAffineQuasicoherentCohomology
import all Linear.NoetherianAffineSchemeActualCohomology
import all Linear.NoetherianInjectiveArtinRees
import all Linear.NoetherianInjectiveCompatibleFractions
import all Linear.NoetherianInjectiveStructureSheafSections
import all Linear.NoetherianInjectiveTildeFlasque
import all Linear.NoetherianOrderedAffineCoverActualHComparison
import all Linear.NoetherianOrderedAffineCoverNativeH
import all Linear.NoetherianOrderedCechHCoefficientNaturality
import all Linear.NormalizationChartConstants
import all Linear.NormalizationChartScalarComparison
import all Linear.NormalizationHomogeneousChartMap
import all Linear.NormalizationHomogeneousCoefficientProjection
import all Linear.NormalizationHomogeneousCombination
import all Linear.NormalizationSourceChartLinearMap
import all Linear.NormalizationSourceChartMembership
import all Linear.NormalizationSourceChartSurjective
import all Linear.NormalizationWeightedChartScalar
import all Linear.OrderedCechActualHCoefficientNaturality
import all Linear.OrderedCechActualHComparison
import all Linear.OrderedCechActualHFactorization
import all Linear.OrderedCechActualHPointwiseNaturality
import all Linear.OrderedCechFullSupport
import all Linear.OrderedCechModuleScalarNaturality
import all Linear.OrderedCechNativeHVanishing
import all Linear.OrderedCechSupportAlternating
import all Linear.OrderedCechSupportContraction
import all Linear.OrderedCechSupportZero
import all Linear.OrderedConstantCechBottomContraction
import all Linear.OrderedConstantCechFiniteContraction
import all Linear.OrderedContainedCechTuples
import all Linear.OrderedCrossSpaceAbelianCechIso
import all Linear.OrderedCrossSpaceCechEndomorphism
import all Linear.OrderedFormalCechCoefficientFunctor
import all Linear.OrderedFormalCechComplex
import all Linear.OrderedFormalCechFunctoriality
import all Linear.OrderedFormalCechWhiskeringNaturality
import all Linear.OrderedFormalHomCochainIso
import all Linear.OrderedFormalHomCoefficientNaturality
import all Linear.OrderedFreeAbelianPresheafComplex
import all Linear.OrderedFreePresheafValueExact
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeSpecifiedNormalizationTopDualityKForget","Linear.NativeSpecifiedNormalizationTopDualityKLinearIso","Linear.NativeSpecifiedNormalizationTopDualityScalar","Linear.NativeSpecifiedNormalizationTopPairing","Linear.NativeStructureModuleFraction","Linear.NativeStructureModuleSections","Linear.NativeStructureModuleSheaf","Linear.NativeTwistRegradingMapNaturality","Linear.NativeWeightedAffineSectionsFunctionSurjective","Linear.NativeWeightedProjOpen","Linear.NativeWeightedSourceAmbientSectionEquiv","Linear.NativeWeightedSourceAmbientSectionNamedOverlap","Linear.NativeWeightedSourceAmbientSectionScalar","Linear.NativeWeightedSpecSectionFunctionScalar","Linear.NilpotentEvaluation","Linear.NilpotentEvaluationUnique","Linear.NilpotentRegular","Linear.NoetherianAffineActualCohomology","Linear.NoetherianAffineOpenActualCohomology","Linear.NoetherianAffineQuasicoherentCohomology","Linear.NoetherianAffineSchemeActualCohomology","Linear.NoetherianInjectiveArtinRees","Linear.NoetherianInjectiveCompatibleFractions","Linear.NoetherianInjectiveStructureSheafSections","Linear.NoetherianInjectiveTildeFlasque","Linear.NoetherianOrderedAffineCoverActualHComparison","Linear.NoetherianOrderedAffineCoverNativeH","Linear.NoetherianOrderedCechHCoefficientNaturality","Linear.NormalizationChartConstants","Linear.NormalizationChartScalarComparison","Linear.NormalizationHomogeneousChartMap","Linear.NormalizationHomogeneousCoefficientProjection","Linear.NormalizationHomogeneousCombination","Linear.NormalizationSourceChartLinearMap","Linear.NormalizationSourceChartMembership","Linear.NormalizationSourceChartSurjective","Linear.NormalizationWeightedChartScalar","Linear.OrderedCechActualHCoefficientNaturality","Linear.OrderedCechActualHComparison","Linear.OrderedCechActualHFactorization","Linear.OrderedCechActualHPointwiseNaturality","Linear.OrderedCechFullSupport","Linear.OrderedCechModuleScalarNaturality","Linear.OrderedCechNativeHVanishing","Linear.OrderedCechSupportAlternating","Linear.OrderedCechSupportContraction","Linear.OrderedCechSupportZero","Linear.OrderedConstantCechBottomContraction","Linear.OrderedConstantCechFiniteContraction","Linear.OrderedContainedCechTuples","Linear.OrderedCrossSpaceAbelianCechIso","Linear.OrderedCrossSpaceCechEndomorphism","Linear.OrderedFormalCechCoefficientFunctor","Linear.OrderedFormalCechComplex","Linear.OrderedFormalCechFunctoriality","Linear.OrderedFormalCechWhiskeringNaturality","Linear.OrderedFormalHomCochainIso","Linear.OrderedFormalHomCoefficientNaturality","Linear.OrderedFreeAbelianPresheafComplex","Linear.OrderedFreePresheafValueExact"]
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
