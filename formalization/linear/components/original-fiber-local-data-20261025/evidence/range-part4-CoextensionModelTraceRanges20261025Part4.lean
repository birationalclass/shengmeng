module
import all Linear.IntegerShiftedFreeRegradingPresentation
import all Linear.IntegerShiftedFreeRelationDualRegrading
import all Linear.IntegerTwistedPresentationCoefficientDualMap
import all Linear.Iteration
import all Linear.JacobianNonzero
import all Linear.JacobianSpecialization
import all Linear.JacobianTrace
import all Linear.KoszulComparison
import all Linear.KoszulFunctionResolution
import all Linear.KoszulHomotopyTop
import all Linear.KoszulResolution
import all Linear.KoszulSocleDeterminant
import all Linear.KoszulSocleMap
import all Linear.KoszulTop
import all Linear.LaurentExponentLocalization
import all Linear.LaurentMonomialBasis
import all Linear.LiftedParameterCoordinates
import all Linear.LiftedParameterMaps
import all Linear.LiftedParameterPresentation
import all Linear.LiftedParametersRegular
import all Linear.LocalFiber
import all Linear.LocalResidueEvaluation
import all Linear.LocalizedAnnihilator
import all Linear.LocalizedModuleAwayOverlap
import all Linear.LocalizedModuleAwayOverlapFraction
import all Linear.LocalizedModuleAwayOverlapRefinement
import all Linear.LocalizedModuleAwayOverlapSemilinear
import all Linear.LocalizedModuleRefinement
import all Linear.LocalizedModuleRefinementComposition
import all Linear.LocalizedModuleRefinementSemilinear
import all Linear.LocalizedSectionFunctionSurjective
import all Linear.ModuleAffineSectionsExact
import all Linear.ModuleBaseCechBasic
import all Linear.ModuleBaseCechFactors
import all Linear.ModuleBaseSourceLocalization
import all Linear.ModuleBaseSourceOverlap
import all Linear.ModuleBaseSourceOverlapRefinement
import all Linear.ModuleCechScHomologyNaturality
import all Linear.ModuleFormalCoproductAdditive
import all Linear.ModuleHomologyForgettingNaturality
import all Linear.ModuleOrderedBaseCech
import all Linear.ModuleOrderedBaseCechExact
import all Linear.ModuleOrderedBaseCechFunctor
import all Linear.ModuleOrderedCechAugmentation
import all Linear.ModuleSheafificationCounitHomEquiv
import all Linear.ModuleShortComplexTopQuotientNaturality
import all Linear.ModuleTopHomologyCokernelData
import all Linear.ModuleTopHomologyScalar
import all Linear.NativeBaseSourceBaseChartInjective
import all Linear.NativeBaseSourceChartBijection
import all Linear.NativeBaseSourceChartSections
import all Linear.NativeBaseSourceSectionsOverlap
import all Linear.NativeBaseSourceWeightedSectionsLinear
import all Linear.NativeCanonicalPolynomialEntryDuality
import all Linear.NativeCechComplexDegreeTransport
import all Linear.NativeChartSectionsModuleNaturality
import all Linear.NativeCoextensionSpecifiedEvaluationTrace
import all Linear.NativeCoextensionSpecifiedTraceInjective
import all Linear.NativeCoextensionSpecifiedTraceProperties
import all Linear.NativeCoextensionSpecifiedTraceScalarRigidity
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.IntegerShiftedFreeRegradingPresentation","Linear.IntegerShiftedFreeRelationDualRegrading","Linear.IntegerTwistedPresentationCoefficientDualMap","Linear.Iteration","Linear.JacobianNonzero","Linear.JacobianSpecialization","Linear.JacobianTrace","Linear.KoszulComparison","Linear.KoszulFunctionResolution","Linear.KoszulHomotopyTop","Linear.KoszulResolution","Linear.KoszulSocleDeterminant","Linear.KoszulSocleMap","Linear.KoszulTop","Linear.LaurentExponentLocalization","Linear.LaurentMonomialBasis","Linear.LiftedParameterCoordinates","Linear.LiftedParameterMaps","Linear.LiftedParameterPresentation","Linear.LiftedParametersRegular","Linear.LocalFiber","Linear.LocalResidueEvaluation","Linear.LocalizedAnnihilator","Linear.LocalizedModuleAwayOverlap","Linear.LocalizedModuleAwayOverlapFraction","Linear.LocalizedModuleAwayOverlapRefinement","Linear.LocalizedModuleAwayOverlapSemilinear","Linear.LocalizedModuleRefinement","Linear.LocalizedModuleRefinementComposition","Linear.LocalizedModuleRefinementSemilinear","Linear.LocalizedSectionFunctionSurjective","Linear.ModuleAffineSectionsExact","Linear.ModuleBaseCechBasic","Linear.ModuleBaseCechFactors","Linear.ModuleBaseSourceLocalization","Linear.ModuleBaseSourceOverlap","Linear.ModuleBaseSourceOverlapRefinement","Linear.ModuleCechScHomologyNaturality","Linear.ModuleFormalCoproductAdditive","Linear.ModuleHomologyForgettingNaturality","Linear.ModuleOrderedBaseCech","Linear.ModuleOrderedBaseCechExact","Linear.ModuleOrderedBaseCechFunctor","Linear.ModuleOrderedCechAugmentation","Linear.ModuleSheafificationCounitHomEquiv","Linear.ModuleShortComplexTopQuotientNaturality","Linear.ModuleTopHomologyCokernelData","Linear.ModuleTopHomologyScalar","Linear.NativeBaseSourceBaseChartInjective","Linear.NativeBaseSourceChartBijection","Linear.NativeBaseSourceChartSections","Linear.NativeBaseSourceSectionsOverlap","Linear.NativeBaseSourceWeightedSectionsLinear","Linear.NativeCanonicalPolynomialEntryDuality","Linear.NativeCechComplexDegreeTransport","Linear.NativeChartSectionsModuleNaturality","Linear.NativeCoextensionSpecifiedEvaluationTrace","Linear.NativeCoextensionSpecifiedTraceInjective","Linear.NativeCoextensionSpecifiedTraceProperties","Linear.NativeCoextensionSpecifiedTraceScalarRigidity"]
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
