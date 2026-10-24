module
import all Linear.SchemeModuleOriginalKoszulPushIntrinsicZero
import all Linear.SchemeModuleOriginalNatBoundaryStep
import all Linear.SchemeModuleOriginalNatClassImage
import all Linear.SchemeModuleOriginalNatTargetExt
import all Linear.SchemeModuleOriginalOpcycleExtComparison
import all Linear.SchemeModuleOriginalOpcycleExtIndex
import all Linear.SchemeModuleOriginalOpcycleSourceIso
import all Linear.SchemeModuleOriginalOpenKoszulCut
import all Linear.SchemeModuleOriginalOpenKoszulCutStatement
import all Linear.SchemeModuleOriginalOpenKoszulCutZero
import all Linear.SchemeModuleOriginalOpenKoszulQCCutStatement
import all Linear.SchemeModuleOriginalPositiveBoundaryIso
import all Linear.SchemeModuleOriginalSmallClassBoundary
import all Linear.SchemeModuleOriginalSmallClassInternalImage
import all Linear.SchemeModuleOriginalTopInitialClassEmbedding
import all Linear.SchemeModuleOriginalWholeTopCokernel
import all Linear.SchemeModuleOriginalWholeTopCokernelStatement
import all Linear.SchemeModuleOverHomology
import all Linear.SchemeModulePushforwardOpenSupport
import all Linear.SchemeModuleRestrictionCokernel
import all Linear.SchemeModuleSpecChartSections
import all Linear.SchemeModuleSpecChartSectionsLinear
import all Linear.SchemeModuleSpecChartSectionsNaturality
import all Linear.SchemeModuleSupportedInternalHomClass
import all Linear.SchemeModuleSupportedRestrictionIso
import all Linear.SchemeModuleSupportedRestrictionUnit
import all Linear.SchemeModuleSupportedSubHomFlasque
import all Linear.SchemeModuleSupportedUnitHomLifting
import all Linear.SchemeModuleUnitHomIso
import all Linear.SchemeModuleUnitHomSections
import all Linear.SchemeModuleUnitInternalExt
import all Linear.SchemeModuleZeroFromOpenCover
import all Linear.SchemeSpecOriginalQuotientFactorSquare
import all Linear.SheafEmbeddingSectionTransport
import all Linear.SheafFreePresentationOfExact
import all Linear.ShortExactInjectiveBoundaryComponents
import all Linear.ShortExactInjectiveExtBoundaryAllDegrees
import all Linear.ShortExactInjectiveNativeBoundaryComponents
import all Linear.ShortExactInjectiveNativeLifts
import all Linear.SmoothCommonCoordinates
import all Linear.SmoothCommonFormalCoordinates
import all Linear.SmoothConormal
import all Linear.SmoothCoordinateRank
import all Linear.SmoothCoordinateSplit
import all Linear.SmoothCotangentDimension
import all Linear.SmoothFixedConormalRank
import all Linear.SmoothFormalCoordinates
import all Linear.SmoothFormalQuotient
import all Linear.SmoothJacobianMinor
import all Linear.SmoothLocusCoordinates
import all Linear.SmoothPointPrincipalOpen
import all Linear.SmoothPolynomialGenerators
import all Linear.SmoothRationalPoint
import all Linear.SmoothReindexedFormalIdeal
import all Linear.SmoothTargetFirstOrder
import all Linear.SmoothTargetParameters
import all Linear.SoclePairing
import all Linear.SocleTransport
import all Linear.SplitJacobianRank
import all Linear.Target
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.SchemeModuleOriginalKoszulPushIntrinsicZero","Linear.SchemeModuleOriginalNatBoundaryStep","Linear.SchemeModuleOriginalNatClassImage","Linear.SchemeModuleOriginalNatTargetExt","Linear.SchemeModuleOriginalOpcycleExtComparison","Linear.SchemeModuleOriginalOpcycleExtIndex","Linear.SchemeModuleOriginalOpcycleSourceIso","Linear.SchemeModuleOriginalOpenKoszulCut","Linear.SchemeModuleOriginalOpenKoszulCutStatement","Linear.SchemeModuleOriginalOpenKoszulCutZero","Linear.SchemeModuleOriginalOpenKoszulQCCutStatement","Linear.SchemeModuleOriginalPositiveBoundaryIso","Linear.SchemeModuleOriginalSmallClassBoundary","Linear.SchemeModuleOriginalSmallClassInternalImage","Linear.SchemeModuleOriginalTopInitialClassEmbedding","Linear.SchemeModuleOriginalWholeTopCokernel","Linear.SchemeModuleOriginalWholeTopCokernelStatement","Linear.SchemeModuleOverHomology","Linear.SchemeModulePushforwardOpenSupport","Linear.SchemeModuleRestrictionCokernel","Linear.SchemeModuleSpecChartSections","Linear.SchemeModuleSpecChartSectionsLinear","Linear.SchemeModuleSpecChartSectionsNaturality","Linear.SchemeModuleSupportedInternalHomClass","Linear.SchemeModuleSupportedRestrictionIso","Linear.SchemeModuleSupportedRestrictionUnit","Linear.SchemeModuleSupportedSubHomFlasque","Linear.SchemeModuleSupportedUnitHomLifting","Linear.SchemeModuleUnitHomIso","Linear.SchemeModuleUnitHomSections","Linear.SchemeModuleUnitInternalExt","Linear.SchemeModuleZeroFromOpenCover","Linear.SchemeSpecOriginalQuotientFactorSquare","Linear.SheafEmbeddingSectionTransport","Linear.SheafFreePresentationOfExact","Linear.ShortExactInjectiveBoundaryComponents","Linear.ShortExactInjectiveExtBoundaryAllDegrees","Linear.ShortExactInjectiveNativeBoundaryComponents","Linear.ShortExactInjectiveNativeLifts","Linear.SmoothCommonCoordinates","Linear.SmoothCommonFormalCoordinates","Linear.SmoothConormal","Linear.SmoothCoordinateRank","Linear.SmoothCoordinateSplit","Linear.SmoothCotangentDimension","Linear.SmoothFixedConormalRank","Linear.SmoothFormalCoordinates","Linear.SmoothFormalQuotient","Linear.SmoothJacobianMinor","Linear.SmoothLocusCoordinates","Linear.SmoothPointPrincipalOpen","Linear.SmoothPolynomialGenerators","Linear.SmoothRationalPoint","Linear.SmoothReindexedFormalIdeal","Linear.SmoothTargetFirstOrder","Linear.SmoothTargetParameters","Linear.SoclePairing","Linear.SocleTransport","Linear.SplitJacobianRank","Linear.Target"]
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
