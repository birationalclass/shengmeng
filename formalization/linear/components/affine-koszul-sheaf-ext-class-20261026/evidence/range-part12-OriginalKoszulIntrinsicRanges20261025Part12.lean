module
import all Linear.SchemeModuleHomSourceBoundaryCokernel
import all Linear.SchemeModuleHomToInternalExtZero
import all Linear.SchemeModuleHomTopSections
import all Linear.SchemeModuleHomTransportIso
import all Linear.SchemeModuleHomUnitCurry
import all Linear.SchemeModuleHomUnitFrameZero
import all Linear.SchemeModuleHomUnitSourceNaturality
import all Linear.SchemeModuleHomZeroBoundaryCokernel
import all Linear.SchemeModuleHomZeroInjectiveClass
import all Linear.SchemeModuleHomZeroInjectiveCycle
import all Linear.SchemeModuleHomZeroSourceNaturality
import all Linear.SchemeModuleHomZeroSourceSupport
import all Linear.SchemeModuleInjectiveCocycleBoundary
import all Linear.SchemeModuleInjectiveCocycleEvaluation
import all Linear.SchemeModuleInjectiveHomEpi
import all Linear.SchemeModuleInjectiveHomExact
import all Linear.SchemeModuleInjectiveInternalHomBoundaryClass
import all Linear.SchemeModuleInjectiveInternalHomCycleSurjective
import all Linear.SchemeModuleInjectiveInternalHomCycles
import all Linear.SchemeModuleInjectiveInternalHomNaturality
import all Linear.SchemeModuleInjectiveInternalHomSourceNaturality
import all Linear.SchemeModuleInternalExtBoundarySourceNaturality
import all Linear.SchemeModuleInternalExtSourceAdditive
import all Linear.SchemeModuleInternalExtSourceBoundary
import all Linear.SchemeModuleInternalExtSourceBoundaryCokernel
import all Linear.SchemeModuleInternalExtSourceBoundaryExact
import all Linear.SchemeModuleInternalExtSourceBoundaryIso
import all Linear.SchemeModuleInternalExtSourceBoundaryNaturality
import all Linear.SchemeModuleInternalExtSourceExact
import all Linear.SchemeModuleInternalExtSourceMap
import all Linear.SchemeModuleInternalExtZero
import all Linear.SchemeModuleInternalExtZeroSource
import all Linear.SchemeModuleInternalHomBifunctor
import all Linear.SchemeModuleInternalHomCoefficientFunctor
import all Linear.SchemeModuleInternalHomCoefficientLimits
import all Linear.SchemeModuleInternalHomComplex
import all Linear.SchemeModuleInternalHomSourceLimits
import all Linear.SchemeModuleInternalHomSourceShortExact
import all Linear.SchemeModuleIsoOnActualCover
import all Linear.SchemeModuleIsoPushforwardRestriction
import all Linear.SchemeModuleLocalHomPrecompose
import all Linear.SchemeModuleLocalHomSourceIso
import all Linear.SchemeModuleLocalInternalExtIso
import all Linear.SchemeModuleOpenInjectives
import all Linear.SchemeModuleOpenKoszulChartData
import all Linear.SchemeModuleOpenKoszulChartDataCutZero
import all Linear.SchemeModuleOpenKoszulDataFromMappedPresentation
import all Linear.SchemeModuleOpenKoszulDataSourceEq
import all Linear.SchemeModuleOpenKoszulIntrinsicZero
import all Linear.SchemeModuleOpenQuasicoherentCoefficientIso
import all Linear.SchemeModuleOpenRestrictionExact
import all Linear.SchemeModuleOriginalBoundaryEmbedding
import all Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit
import all Linear.SchemeModuleOriginalBoundarySequenceComparison
import all Linear.SchemeModuleOriginalBoundaryStepNaturality
import all Linear.SchemeModuleOriginalChainInternalBoundaryClass
import all Linear.SchemeModuleOriginalClassGlobalToLocal
import all Linear.SchemeModuleOriginalCutCokernelTarget
import all Linear.SchemeModuleOriginalCutStructurePushforward
import all Linear.SchemeModuleOriginalFirstBoundaryCokernel
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.SchemeModuleHomSourceBoundaryCokernel","Linear.SchemeModuleHomToInternalExtZero","Linear.SchemeModuleHomTopSections","Linear.SchemeModuleHomTransportIso","Linear.SchemeModuleHomUnitCurry","Linear.SchemeModuleHomUnitFrameZero","Linear.SchemeModuleHomUnitSourceNaturality","Linear.SchemeModuleHomZeroBoundaryCokernel","Linear.SchemeModuleHomZeroInjectiveClass","Linear.SchemeModuleHomZeroInjectiveCycle","Linear.SchemeModuleHomZeroSourceNaturality","Linear.SchemeModuleHomZeroSourceSupport","Linear.SchemeModuleInjectiveCocycleBoundary","Linear.SchemeModuleInjectiveCocycleEvaluation","Linear.SchemeModuleInjectiveHomEpi","Linear.SchemeModuleInjectiveHomExact","Linear.SchemeModuleInjectiveInternalHomBoundaryClass","Linear.SchemeModuleInjectiveInternalHomCycleSurjective","Linear.SchemeModuleInjectiveInternalHomCycles","Linear.SchemeModuleInjectiveInternalHomNaturality","Linear.SchemeModuleInjectiveInternalHomSourceNaturality","Linear.SchemeModuleInternalExtBoundarySourceNaturality","Linear.SchemeModuleInternalExtSourceAdditive","Linear.SchemeModuleInternalExtSourceBoundary","Linear.SchemeModuleInternalExtSourceBoundaryCokernel","Linear.SchemeModuleInternalExtSourceBoundaryExact","Linear.SchemeModuleInternalExtSourceBoundaryIso","Linear.SchemeModuleInternalExtSourceBoundaryNaturality","Linear.SchemeModuleInternalExtSourceExact","Linear.SchemeModuleInternalExtSourceMap","Linear.SchemeModuleInternalExtZero","Linear.SchemeModuleInternalExtZeroSource","Linear.SchemeModuleInternalHomBifunctor","Linear.SchemeModuleInternalHomCoefficientFunctor","Linear.SchemeModuleInternalHomCoefficientLimits","Linear.SchemeModuleInternalHomComplex","Linear.SchemeModuleInternalHomSourceLimits","Linear.SchemeModuleInternalHomSourceShortExact","Linear.SchemeModuleIsoOnActualCover","Linear.SchemeModuleIsoPushforwardRestriction","Linear.SchemeModuleLocalHomPrecompose","Linear.SchemeModuleLocalHomSourceIso","Linear.SchemeModuleLocalInternalExtIso","Linear.SchemeModuleOpenInjectives","Linear.SchemeModuleOpenKoszulChartData","Linear.SchemeModuleOpenKoszulChartDataCutZero","Linear.SchemeModuleOpenKoszulDataFromMappedPresentation","Linear.SchemeModuleOpenKoszulDataSourceEq","Linear.SchemeModuleOpenKoszulIntrinsicZero","Linear.SchemeModuleOpenQuasicoherentCoefficientIso","Linear.SchemeModuleOpenRestrictionExact","Linear.SchemeModuleOriginalBoundaryEmbedding","Linear.SchemeModuleOriginalBoundaryEmbeddingExplicit","Linear.SchemeModuleOriginalBoundarySequenceComparison","Linear.SchemeModuleOriginalBoundaryStepNaturality","Linear.SchemeModuleOriginalChainInternalBoundaryClass","Linear.SchemeModuleOriginalClassGlobalToLocal","Linear.SchemeModuleOriginalCutCokernelTarget","Linear.SchemeModuleOriginalCutStructurePushforward","Linear.SchemeModuleOriginalFirstBoundaryCokernel"]
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
