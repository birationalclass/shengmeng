module
import all Linear.NilpotentEvaluation
import all Linear.NilpotentEvaluationUnique
import all Linear.NilpotentRegular
import all Linear.NoetherNormalizationKrull
import all Linear.NoetherNormalizationTranscendence
import all Linear.NormalizationDifferentialRank
import all Linear.OriginRegular
import all Linear.OriginalChainIteratedSourceBoundary
import all Linear.OriginalChainOpcycleEmbedding
import all Linear.OriginalChainOpcycleIndex
import all Linear.OriginalChainTerminalSourceIso
import all Linear.OriginalChainTopExtUniverse
import all Linear.OriginalChainTopOpcycleEmbedding
import all Linear.OriginalGlobalModuleScalar
import all Linear.OriginalIdealFirstOrder
import all Linear.OriginalPolynomialNormal
import all Linear.OriginalProjectiveWeightedChartScalarTransport
import all Linear.OriginalProjectiveWeightedChartSectionRing
import all Linear.OriginalProjectiveZeroChart
import all Linear.OverOpenInjectiveRestriction
import all Linear.OverOpenZeroPresheaf
import all Linear.OverOpenZeroPresheafAdjunction
import all Linear.OverOpenZeroPresheafFunctor
import all Linear.OverOpenZeroSheafAdjunction
import all Linear.OverOpenZeroSheafFunctor
import all Linear.PairingMatrix
import all Linear.ParameterFamilyEnrichWitness
import all Linear.ParameterLinearPart
import all Linear.ParameterPairingChange
import all Linear.ParameterPolynomialFamilyIntersection
import all Linear.ParameterQuotient
import all Linear.ParameterSubstitution
import all Linear.PointDecomposition
import all Linear.PointLocalCoordinateEquiv
import all Linear.PolynomialApproximation
import all Linear.PolynomialContraction
import all Linear.PolynomialDiagonal
import all Linear.PolynomialDifferenceDegree
import all Linear.PolynomialDoubleFiber
import all Linear.PolynomialFiberDiagonal
import all Linear.PolynomialFilteredImage
import all Linear.PolynomialFiniteZeroLocus
import all Linear.PolynomialFirstJet
import all Linear.PolynomialFormalCompletion
import all Linear.PolynomialFormalDerivative
import all Linear.PolynomialFormalFiber
import all Linear.PolynomialGlobalResidue
import all Linear.PolynomialGrowthDegreeComparison
import all Linear.PolynomialGrowthLeadingCoeff
import all Linear.PolynomialGrowthLimits
import all Linear.PolynomialGrowthRank
import all Linear.PolynomialLinearChange
import all Linear.PolynomialLinearGrading
import all Linear.PolynomialLinearHighestComponents
import all Linear.PolynomialLocalCutRegular
import all Linear.PolynomialLocalParameters
import all Linear.PolynomialMapFibersFinite
import all Linear.PolynomialNormalEquations
import all Linear.PolynomialOriginFinite
import all Linear.PolynomialPointCompletion
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NilpotentEvaluation","Linear.NilpotentEvaluationUnique","Linear.NilpotentRegular","Linear.NoetherNormalizationKrull","Linear.NoetherNormalizationTranscendence","Linear.NormalizationDifferentialRank","Linear.OriginRegular","Linear.OriginalChainIteratedSourceBoundary","Linear.OriginalChainOpcycleEmbedding","Linear.OriginalChainOpcycleIndex","Linear.OriginalChainTerminalSourceIso","Linear.OriginalChainTopExtUniverse","Linear.OriginalChainTopOpcycleEmbedding","Linear.OriginalGlobalModuleScalar","Linear.OriginalIdealFirstOrder","Linear.OriginalPolynomialNormal","Linear.OriginalProjectiveWeightedChartScalarTransport","Linear.OriginalProjectiveWeightedChartSectionRing","Linear.OriginalProjectiveZeroChart","Linear.OverOpenInjectiveRestriction","Linear.OverOpenZeroPresheaf","Linear.OverOpenZeroPresheafAdjunction","Linear.OverOpenZeroPresheafFunctor","Linear.OverOpenZeroSheafAdjunction","Linear.OverOpenZeroSheafFunctor","Linear.PairingMatrix","Linear.ParameterFamilyEnrichWitness","Linear.ParameterLinearPart","Linear.ParameterPairingChange","Linear.ParameterPolynomialFamilyIntersection","Linear.ParameterQuotient","Linear.ParameterSubstitution","Linear.PointDecomposition","Linear.PointLocalCoordinateEquiv","Linear.PolynomialApproximation","Linear.PolynomialContraction","Linear.PolynomialDiagonal","Linear.PolynomialDifferenceDegree","Linear.PolynomialDoubleFiber","Linear.PolynomialFiberDiagonal","Linear.PolynomialFilteredImage","Linear.PolynomialFiniteZeroLocus","Linear.PolynomialFirstJet","Linear.PolynomialFormalCompletion","Linear.PolynomialFormalDerivative","Linear.PolynomialFormalFiber","Linear.PolynomialGlobalResidue","Linear.PolynomialGrowthDegreeComparison","Linear.PolynomialGrowthLeadingCoeff","Linear.PolynomialGrowthLimits","Linear.PolynomialGrowthRank","Linear.PolynomialLinearChange","Linear.PolynomialLinearGrading","Linear.PolynomialLinearHighestComponents","Linear.PolynomialLocalCutRegular","Linear.PolynomialLocalParameters","Linear.PolynomialMapFibersFinite","Linear.PolynomialNormalEquations","Linear.PolynomialOriginFinite","Linear.PolynomialPointCompletion"]
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
