module
import all Linear.ActualAbelianSheafConstantPullback
import all Linear.ActualPresentationDualKernel
import all Linear.ActualPresentationGradedDualKernel
import all Linear.AdditiveStalkExactFromNearbySections
import all Linear.AffineChartComparison
import all Linear.AffineDiagonal
import all Linear.AffineFiltered
import all Linear.AffineFinitePresentationInternalHomQuasicoherent
import all Linear.AffineFunctional
import all Linear.AffineKoszulFramedHomCokernel
import all Linear.AffineKoszulGeometricClassZero
import all Linear.AffineKoszulGeometricRestriction
import all Linear.AffineKoszulHomCoefficientRestriction
import all Linear.AffineKoszulHomGeometricCokernel
import all Linear.AffineKoszulIntrinsicPullbackZero
import all Linear.AffineKoszulTermInternalDualHom
import all Linear.AffinePushforwardGlobalSectionsNaturality
import all Linear.AffineQuasicoherentComplexCounit
import all Linear.AffineQuasicoherentHomActualOpenEvaluation
import all Linear.AffineQuasicoherentHomActualOpenSections
import all Linear.AffineQuasicoherentHomOpenSections
import all Linear.AffineQuasicoherentSourceMorphisms
import all Linear.AffineRationalPointValues
import all Linear.AffineTildeFinitePresentationHomIso
import all Linear.AffineTildeFinitePresentationInternalHom
import all Linear.AffineTildeHomPrecompositionValues
import all Linear.AffineTildeHomTargetNaturality
import all Linear.AffineTildePullbackExtendScalars
import all Linear.AffineTildePullbackUnit
import all Linear.AffineTildePullbackUnitValues
import all Linear.AffineTildeTensorPullback
import all Linear.AffineTildeTensorPullbackUnit
import all Linear.ArbitraryParameterJacobian
import all Linear.ArbitraryParameterSocle
import all Linear.ArtinianCompletion
import all Linear.ArtinianDiagonal
import all Linear.ArtinianGlobalPairing
import all Linear.AwayFractionEmbedding
import all Linear.AwayFractionUnramified
import all Linear.AwayQuotientComparison
import all Linear.BoundedPolynomialCombination
import all Linear.CenteredRelativeJacobian
import all Linear.ChainActualCokernelAugmentation
import all Linear.ChainActualCokernelTargetAugmentation
import all Linear.ChainExplicitStandardTopExtClass
import all Linear.ChainExplicitTopExtNaturality
import all Linear.ChainFirstCokernelIso
import all Linear.ChainFirstCokernelZero
import all Linear.ChainResolutionAsCochain
import all Linear.ChainResolutionTopExtClass
import all Linear.ChainStandardTopExtClass
import all Linear.ChosenProjectiveNormalizationDimensions
import all Linear.ClosedDiscreteSupportSheafFlasque
import all Linear.CochainAugmentationOpcycle
import all Linear.CochainAugmentedTopHomotopyComponents
import all Linear.CochainClassEqBoundary
import all Linear.CochainCocycleOfHomShifted
import all Linear.CochainConeLiftClassAllDegrees
import all Linear.CochainConeLiftClassBridge
import all Linear.CochainConeLiftDerivedAllDegrees
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.ActualAbelianSheafConstantPullback","Linear.ActualPresentationDualKernel","Linear.ActualPresentationGradedDualKernel","Linear.AdditiveStalkExactFromNearbySections","Linear.AffineChartComparison","Linear.AffineDiagonal","Linear.AffineFiltered","Linear.AffineFinitePresentationInternalHomQuasicoherent","Linear.AffineFunctional","Linear.AffineKoszulFramedHomCokernel","Linear.AffineKoszulGeometricClassZero","Linear.AffineKoszulGeometricRestriction","Linear.AffineKoszulHomCoefficientRestriction","Linear.AffineKoszulHomGeometricCokernel","Linear.AffineKoszulIntrinsicPullbackZero","Linear.AffineKoszulTermInternalDualHom","Linear.AffinePushforwardGlobalSectionsNaturality","Linear.AffineQuasicoherentComplexCounit","Linear.AffineQuasicoherentHomActualOpenEvaluation","Linear.AffineQuasicoherentHomActualOpenSections","Linear.AffineQuasicoherentHomOpenSections","Linear.AffineQuasicoherentSourceMorphisms","Linear.AffineRationalPointValues","Linear.AffineTildeFinitePresentationHomIso","Linear.AffineTildeFinitePresentationInternalHom","Linear.AffineTildeHomPrecompositionValues","Linear.AffineTildeHomTargetNaturality","Linear.AffineTildePullbackExtendScalars","Linear.AffineTildePullbackUnit","Linear.AffineTildePullbackUnitValues","Linear.AffineTildeTensorPullback","Linear.AffineTildeTensorPullbackUnit","Linear.ArbitraryParameterJacobian","Linear.ArbitraryParameterSocle","Linear.ArtinianCompletion","Linear.ArtinianDiagonal","Linear.ArtinianGlobalPairing","Linear.AwayFractionEmbedding","Linear.AwayFractionUnramified","Linear.AwayQuotientComparison","Linear.BoundedPolynomialCombination","Linear.CenteredRelativeJacobian","Linear.ChainActualCokernelAugmentation","Linear.ChainActualCokernelTargetAugmentation","Linear.ChainExplicitStandardTopExtClass","Linear.ChainExplicitTopExtNaturality","Linear.ChainFirstCokernelIso","Linear.ChainFirstCokernelZero","Linear.ChainResolutionAsCochain","Linear.ChainResolutionTopExtClass","Linear.ChainStandardTopExtClass","Linear.ChosenProjectiveNormalizationDimensions","Linear.ClosedDiscreteSupportSheafFlasque","Linear.CochainAugmentationOpcycle","Linear.CochainAugmentedTopHomotopyComponents","Linear.CochainClassEqBoundary","Linear.CochainCocycleOfHomShifted","Linear.CochainConeLiftClassAllDegrees","Linear.CochainConeLiftClassBridge","Linear.CochainConeLiftDerivedAllDegrees"]
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
