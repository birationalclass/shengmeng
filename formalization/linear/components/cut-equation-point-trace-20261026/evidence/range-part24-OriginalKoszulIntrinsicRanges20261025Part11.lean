module
import all Linear.SchemeModuleActualStalkOpenRestriction
import all Linear.SchemeModuleActualStalkOpenRestrictionReverse
import all Linear.SchemeModuleAdditiveSheafColimits
import all Linear.SchemeModuleBiproductInternalExt
import all Linear.SchemeModuleCanonicalGlobalToInternalExt
import all Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary
import all Linear.SchemeModuleChainOpcycleExtShift
import all Linear.SchemeModuleChainOpcycleSequence
import all Linear.SchemeModuleChainOpenKoszulHomCokernel
import all Linear.SchemeModuleChainTopOpcycleIso
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExt
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections
import all Linear.SchemeModuleCochainInternalBoundaryStep
import all Linear.SchemeModuleCochainIteratedInternalBoundary
import all Linear.SchemeModuleCochainResolutionInternalBoundaryClass
import all Linear.SchemeModuleCocycleToInternalExtSourceNaturality
import all Linear.SchemeModuleDerivedInternalHom
import all Linear.SchemeModuleFiniteFreeFrameInternalExt
import all Linear.SchemeModuleFiniteFreeInternalExt
import all Linear.SchemeModuleFiniteLocallyFreeInternalExt
import all Linear.SchemeModuleFiniteSupportCohomology
import all Linear.SchemeModuleFiniteSupportLambdaSourceIso
import all Linear.SchemeModuleFlasqueKernelSectionLifting
import all Linear.SchemeModuleFreeOverIso
import all Linear.SchemeModuleGeometricPullbackZero
import all Linear.SchemeModuleGlobalSectionMorphism
import all Linear.SchemeModuleGlobalToInternalExt
import all Linear.SchemeModuleGlobalToInternalExtAllDegrees
import all Linear.SchemeModuleGlobalToInternalExtBoundary
import all Linear.SchemeModuleGlobalToInternalExtCocycle
import all Linear.SchemeModuleGlobalToInternalExtIteration
import all Linear.SchemeModuleGlobalToInternalExtNaturality
import all Linear.SchemeModuleGlobalToInternalExtSourceIso
import all Linear.SchemeModuleGlobalToInternalExtSourceNaturality
import all Linear.SchemeModuleGlobalToInternalExtZeroBoundary
import all Linear.SchemeModuleHomAffineChartSections
import all Linear.SchemeModuleHomArrowCokernel
import all Linear.SchemeModuleHomEvaluationRestriction
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomOpenEvaluation
import all Linear.SchemeModuleHomOpenImmersionBijective
import all Linear.SchemeModuleHomOpenImmersionCokernel
import all Linear.SchemeModuleHomOpenImmersionCokernelClass
import all Linear.SchemeModuleHomOpenImmersionCurry
import all Linear.SchemeModuleHomOpenImmersionIso
import all Linear.SchemeModuleHomOpenImmersionMorphism
import all Linear.SchemeModuleHomOpenImmersionRestriction
import all Linear.SchemeModuleHomOpenImmersionSourceNaturality
import all Linear.SchemeModuleHomOpenScalars
import all Linear.SchemeModuleHomPostcompose
import all Linear.SchemeModuleHomPostcomposeSection
import all Linear.SchemeModuleHomPrecompose
import all Linear.SchemeModuleHomPrecomposeComparison
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleHomShortComplexSourceMap
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.SchemeModuleActualStalkOpenRestriction","Linear.SchemeModuleActualStalkOpenRestrictionReverse","Linear.SchemeModuleAdditiveSheafColimits","Linear.SchemeModuleBiproductInternalExt","Linear.SchemeModuleCanonicalGlobalToInternalExt","Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary","Linear.SchemeModuleChainOpcycleExtShift","Linear.SchemeModuleChainOpcycleSequence","Linear.SchemeModuleChainOpenKoszulHomCokernel","Linear.SchemeModuleChainTopOpcycleIso","Linear.SchemeModuleClosedDiscreteGlobalToInternalExt","Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections","Linear.SchemeModuleCochainInternalBoundaryStep","Linear.SchemeModuleCochainIteratedInternalBoundary","Linear.SchemeModuleCochainResolutionInternalBoundaryClass","Linear.SchemeModuleCocycleToInternalExtSourceNaturality","Linear.SchemeModuleDerivedInternalHom","Linear.SchemeModuleFiniteFreeFrameInternalExt","Linear.SchemeModuleFiniteFreeInternalExt","Linear.SchemeModuleFiniteLocallyFreeInternalExt","Linear.SchemeModuleFiniteSupportCohomology","Linear.SchemeModuleFiniteSupportLambdaSourceIso","Linear.SchemeModuleFlasqueKernelSectionLifting","Linear.SchemeModuleFreeOverIso","Linear.SchemeModuleGeometricPullbackZero","Linear.SchemeModuleGlobalSectionMorphism","Linear.SchemeModuleGlobalToInternalExt","Linear.SchemeModuleGlobalToInternalExtAllDegrees","Linear.SchemeModuleGlobalToInternalExtBoundary","Linear.SchemeModuleGlobalToInternalExtCocycle","Linear.SchemeModuleGlobalToInternalExtIteration","Linear.SchemeModuleGlobalToInternalExtNaturality","Linear.SchemeModuleGlobalToInternalExtSourceIso","Linear.SchemeModuleGlobalToInternalExtSourceNaturality","Linear.SchemeModuleGlobalToInternalExtZeroBoundary","Linear.SchemeModuleHomAffineChartSections","Linear.SchemeModuleHomArrowCokernel","Linear.SchemeModuleHomEvaluationRestriction","Linear.SchemeModuleHomGlobal","Linear.SchemeModuleHomModuleSections","Linear.SchemeModuleHomModuleSheaf","Linear.SchemeModuleHomOpenEvaluation","Linear.SchemeModuleHomOpenImmersionBijective","Linear.SchemeModuleHomOpenImmersionCokernel","Linear.SchemeModuleHomOpenImmersionCokernelClass","Linear.SchemeModuleHomOpenImmersionCurry","Linear.SchemeModuleHomOpenImmersionIso","Linear.SchemeModuleHomOpenImmersionMorphism","Linear.SchemeModuleHomOpenImmersionRestriction","Linear.SchemeModuleHomOpenImmersionSourceNaturality","Linear.SchemeModuleHomOpenScalars","Linear.SchemeModuleHomPostcompose","Linear.SchemeModuleHomPostcomposeSection","Linear.SchemeModuleHomPrecompose","Linear.SchemeModuleHomPrecomposeComparison","Linear.SchemeModuleHomPresheaf","Linear.SchemeModuleHomRestriction","Linear.SchemeModuleHomScalar","Linear.SchemeModuleHomSheaf","Linear.SchemeModuleHomShortComplexSourceMap"]
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
