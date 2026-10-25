module
import all Linear.OrderedFreePresheafValueHomCochain
import all Linear.OrderedFreeSheafCechResolution
import all Linear.OrderedFreeSheafHomCoefficientFactors
import all Linear.OrderedFreeSheafHomCoefficientNaturality
import all Linear.OrderedFreeSheafHomCoefficientPresheaf
import all Linear.OrderedFreeSheafHomComplex
import all Linear.OrderedModuleCechActualAbelian
import all Linear.OrderedModuleCechActualAbelianFactorization
import all Linear.OrderedModuleCechActualAbelianHomology
import all Linear.OrderedModuleCechActualAbelianNaturality
import all Linear.OrderedModuleCechActualCoefficientMap
import all Linear.OrderedModuleCechCoefficientFactors
import all Linear.OrderedModuleCechCoefficientScalar
import all Linear.OrderedSimplexBottomInsertion
import all Linear.OrderedToFullFreeFormalCech
import all Linear.OriginalAwayOverlapFraction
import all Linear.OriginalGlobalModuleScalar
import all Linear.OriginalGlobalModuleScalarRingHom
import all Linear.OriginalGlobalModuleScalarRingLaws
import all Linear.OriginalGradedCoextensionAdjoint
import all Linear.OriginalGradedCoextensionAdjointZero
import all Linear.OriginalProjectiveChartScalarTransport
import all Linear.OriginalProjectiveChartSectionRing
import all Linear.OverOpenInjectiveUnitExtension
import all Linear.OverOpenUnitZeroPresheafMono
import all Linear.OverOpenUnitZeroSheafAdjoint
import all Linear.OverOpenUnitZeroSheafBinding
import all Linear.OverOpenUnitZeroSheafMono
import all Linear.OverOpenZeroPresheaf
import all Linear.OverOpenZeroPresheafAdjunction
import all Linear.OverOpenZeroPresheafFunctor
import all Linear.OverOpenZeroSheafAdjunction
import all Linear.OverOpenZeroSheafFunctor
import all Linear.PairingMatrix
import all Linear.ParameterLinearPart
import all Linear.ParameterPairingChange
import all Linear.ParameterQuotient
import all Linear.ParameterSubstitution
import all Linear.PointDecomposition
import all Linear.PointedExactFunctorExtMap
import all Linear.PointedExactFunctorExtMapIsIso
import all Linear.PointedExactFunctorExtZero
import all Linear.PointedExactFunctorExtZeroFullyFaithful
import all Linear.PointedExactFunctorExtZeroHomEquiv
import all Linear.PolynomialApproximation
import all Linear.PolynomialContraction
import all Linear.PolynomialDiagonal
import all Linear.PolynomialDifferenceDegree
import all Linear.PolynomialDoubleFiber
import all Linear.PolynomialFiberDiagonal
import all Linear.PolynomialFormalCompletion
import all Linear.PolynomialFormalDerivative
import all Linear.PolynomialFormalFiber
import all Linear.PolynomialGlobalResidue
import all Linear.PolynomialOriginFinite
import all Linear.PolynomialPointCompletion
import all Linear.PolynomialRecentering
import all Linear.PolynomialRegular
import all Linear.PolynomialSocle
import all Linear.PowerSeriesAugmentation
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.OrderedFreePresheafValueHomCochain","Linear.OrderedFreeSheafCechResolution","Linear.OrderedFreeSheafHomCoefficientFactors","Linear.OrderedFreeSheafHomCoefficientNaturality","Linear.OrderedFreeSheafHomCoefficientPresheaf","Linear.OrderedFreeSheafHomComplex","Linear.OrderedModuleCechActualAbelian","Linear.OrderedModuleCechActualAbelianFactorization","Linear.OrderedModuleCechActualAbelianHomology","Linear.OrderedModuleCechActualAbelianNaturality","Linear.OrderedModuleCechActualCoefficientMap","Linear.OrderedModuleCechCoefficientFactors","Linear.OrderedModuleCechCoefficientScalar","Linear.OrderedSimplexBottomInsertion","Linear.OrderedToFullFreeFormalCech","Linear.OriginalAwayOverlapFraction","Linear.OriginalGlobalModuleScalar","Linear.OriginalGlobalModuleScalarRingHom","Linear.OriginalGlobalModuleScalarRingLaws","Linear.OriginalGradedCoextensionAdjoint","Linear.OriginalGradedCoextensionAdjointZero","Linear.OriginalProjectiveChartScalarTransport","Linear.OriginalProjectiveChartSectionRing","Linear.OverOpenInjectiveUnitExtension","Linear.OverOpenUnitZeroPresheafMono","Linear.OverOpenUnitZeroSheafAdjoint","Linear.OverOpenUnitZeroSheafBinding","Linear.OverOpenUnitZeroSheafMono","Linear.OverOpenZeroPresheaf","Linear.OverOpenZeroPresheafAdjunction","Linear.OverOpenZeroPresheafFunctor","Linear.OverOpenZeroSheafAdjunction","Linear.OverOpenZeroSheafFunctor","Linear.PairingMatrix","Linear.ParameterLinearPart","Linear.ParameterPairingChange","Linear.ParameterQuotient","Linear.ParameterSubstitution","Linear.PointDecomposition","Linear.PointedExactFunctorExtMap","Linear.PointedExactFunctorExtMapIsIso","Linear.PointedExactFunctorExtZero","Linear.PointedExactFunctorExtZeroFullyFaithful","Linear.PointedExactFunctorExtZeroHomEquiv","Linear.PolynomialApproximation","Linear.PolynomialContraction","Linear.PolynomialDiagonal","Linear.PolynomialDifferenceDegree","Linear.PolynomialDoubleFiber","Linear.PolynomialFiberDiagonal","Linear.PolynomialFormalCompletion","Linear.PolynomialFormalDerivative","Linear.PolynomialFormalFiber","Linear.PolynomialGlobalResidue","Linear.PolynomialOriginFinite","Linear.PolynomialPointCompletion","Linear.PolynomialRecentering","Linear.PolynomialRegular","Linear.PolynomialSocle","Linear.PowerSeriesAugmentation"]
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
