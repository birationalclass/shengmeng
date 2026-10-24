module
import all Linear.AbelianOpenSectionIsoTransport
import all Linear.ActualAbelianSheafConstantPullback
import all Linear.ActualAdditiveDualPairing
import all Linear.ActualPresentationDualKernel
import all Linear.ActualPresentationGradedDualKernel
import all Linear.AcyclicChainExtVanishing
import all Linear.AcyclicChainHomExtension
import all Linear.AcyclicChainOpcycleSequence
import all Linear.AcyclicGlobalExtCoefficientNaturality
import all Linear.AcyclicGlobalExtIteratedCoefficientNaturality
import all Linear.AcyclicHomCokernelCoefficientNaturality
import all Linear.AcyclicResolutionCochainComparisonIso
import all Linear.AcyclicResolutionCochainComparisonNaturality
import all Linear.AcyclicResolutionExtVanishing
import all Linear.AcyclicResolutionGlobalExtCokernel
import all Linear.AcyclicResolutionGlobalExtHomology
import all Linear.AcyclicResolutionGlobalExtShift
import all Linear.AcyclicResolutionHomologyCoefficientNaturality
import all Linear.AcyclicResolutionOpcycleCoefficientNaturality
import all Linear.AddMonoidAlgebraLocalization
import all Linear.AdditiveFunctorEndRingHom
import all Linear.AdditiveFunctorScalarSquare
import all Linear.AdjunctionCounitHomEquiv
import all Linear.AffineDiagonal
import all Linear.AffineFiltered
import all Linear.AffineFunctional
import all Linear.AffineQuasicoherentSectionsSurjective
import all Linear.ArbitraryParameterJacobian
import all Linear.ArbitraryParameterSocle
import all Linear.ArtinianCompletion
import all Linear.ArtinianDiagonal
import all Linear.ArtinianGlobalPairing
import all Linear.AugmentedAlternatingWhiskering
import all Linear.AugmentedPointwiseWhiskering
import all Linear.AwayCongr
import all Linear.AwayFractionEmbedding
import all Linear.BaseSourceLocalizedModuleInjective
import all Linear.BiproductMatrixNaturality
import all Linear.CechSupportContraction
import all Linear.CechTuplePermutations
import all Linear.CenteredRelativeJacobian
import all Linear.ChainActualHomCoefficientNaturality
import all Linear.ChainActualHomCycles
import all Linear.ChainActualHomHomologyCoefficientNaturality
import all Linear.ChainExactOfAllHomExact
import all Linear.ChainZeroHomologySameRelations
import all Linear.CoextensionBaseGradeCompatibility
import all Linear.CoextensionDegreeZeroEndEvaluation
import all Linear.CoextensionDegreeZeroRigidity
import all Linear.CoextensionEvaluationAtOne
import all Linear.CoextensionFractionEmbedding
import all Linear.CoextensionFractionFunctional
import all Linear.CoextensionFractionNaturality
import all Linear.CoextensionGradedBaseEquiv
import all Linear.CoextensionGradedModule
import all Linear.CoextensionHomInjective
import all Linear.CoextensionIntegralEmbedding
import all Linear.CoextensionNativeTopDualityInputs
import all Linear.CoextensionProjectiveGradeCompatibility
import all Linear.CompleteIntersectionChange
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.AbelianOpenSectionIsoTransport","Linear.ActualAbelianSheafConstantPullback","Linear.ActualAdditiveDualPairing","Linear.ActualPresentationDualKernel","Linear.ActualPresentationGradedDualKernel","Linear.AcyclicChainExtVanishing","Linear.AcyclicChainHomExtension","Linear.AcyclicChainOpcycleSequence","Linear.AcyclicGlobalExtCoefficientNaturality","Linear.AcyclicGlobalExtIteratedCoefficientNaturality","Linear.AcyclicHomCokernelCoefficientNaturality","Linear.AcyclicResolutionCochainComparisonIso","Linear.AcyclicResolutionCochainComparisonNaturality","Linear.AcyclicResolutionExtVanishing","Linear.AcyclicResolutionGlobalExtCokernel","Linear.AcyclicResolutionGlobalExtHomology","Linear.AcyclicResolutionGlobalExtShift","Linear.AcyclicResolutionHomologyCoefficientNaturality","Linear.AcyclicResolutionOpcycleCoefficientNaturality","Linear.AddMonoidAlgebraLocalization","Linear.AdditiveFunctorEndRingHom","Linear.AdditiveFunctorScalarSquare","Linear.AdjunctionCounitHomEquiv","Linear.AffineDiagonal","Linear.AffineFiltered","Linear.AffineFunctional","Linear.AffineQuasicoherentSectionsSurjective","Linear.ArbitraryParameterJacobian","Linear.ArbitraryParameterSocle","Linear.ArtinianCompletion","Linear.ArtinianDiagonal","Linear.ArtinianGlobalPairing","Linear.AugmentedAlternatingWhiskering","Linear.AugmentedPointwiseWhiskering","Linear.AwayCongr","Linear.AwayFractionEmbedding","Linear.BaseSourceLocalizedModuleInjective","Linear.BiproductMatrixNaturality","Linear.CechSupportContraction","Linear.CechTuplePermutations","Linear.CenteredRelativeJacobian","Linear.ChainActualHomCoefficientNaturality","Linear.ChainActualHomCycles","Linear.ChainActualHomHomologyCoefficientNaturality","Linear.ChainExactOfAllHomExact","Linear.ChainZeroHomologySameRelations","Linear.CoextensionBaseGradeCompatibility","Linear.CoextensionDegreeZeroEndEvaluation","Linear.CoextensionDegreeZeroRigidity","Linear.CoextensionEvaluationAtOne","Linear.CoextensionFractionEmbedding","Linear.CoextensionFractionFunctional","Linear.CoextensionFractionNaturality","Linear.CoextensionGradedBaseEquiv","Linear.CoextensionGradedModule","Linear.CoextensionHomInjective","Linear.CoextensionIntegralEmbedding","Linear.CoextensionNativeTopDualityInputs","Linear.CoextensionProjectiveGradeCompatibility","Linear.CompleteIntersectionChange"]
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
