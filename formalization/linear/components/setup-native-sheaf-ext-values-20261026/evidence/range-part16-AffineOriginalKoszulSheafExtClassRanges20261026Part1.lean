module
import all Linear.AdditiveFunctorExtendComplex
import all Linear.AdditiveFunctorExtendNaturality
import all Linear.AdditiveFunctorExtendSingleCompatibility
import all Linear.AffineKoszulActualModuleExtInternalHomTop
import all Linear.AffineKoszulActualSheafExtTop
import all Linear.AffineKoszulDerivedModuleExtGeometricRestriction
import all Linear.AffineKoszulInternalHomCochain
import all Linear.AffineKoszulInternalHomComplexIso
import all Linear.AffineKoszulInternalHomTopCohomology
import all Linear.AffineKoszulOriginalSheafExtClass
import all Linear.ChainTopExtExactFunctorCompatibility
import all Linear.ChainTopExtExactFunctorMappedChain
import all Linear.CochainResolutionExactFunctorCompatibility
import all Linear.CochainResolutionExactFunctorObjects
import all Linear.CochainResolutionSourceIso
import all Linear.CochainResolutionTargetIso
import all Linear.KoszulExactTopExtCoefficientRestriction
import all Linear.KoszulExactTopExtCoefficients
import all Linear.KoszulNativeHomTopCohomology
import all Linear.KoszulNativeHomTopCokernel
import all Linear.MappedChainCokernelAugmentationSquare
import all Linear.MappedCochainTopCocycle
import all Linear.OriginalChainMappedAugmentationComparison
import all Linear.OriginalChainMappedExtComparison
import all Linear.OriginalChainMappedTopCocycle
import all Linear.OriginalChainTopExtTargetIso
import all Linear.ProjectiveResolutionOriginalChainClass
import all Linear.SchemeModuleAcyclicChainTopInternalExt
import all Linear.SchemeModuleAcyclicCokernelRankExt
import all Linear.SchemeModuleAcyclicCokernelTopInternalExt
import all Linear.SchemeModuleChainSourceAcyclic
import all Linear.SchemeModuleChainTopHomology
import all Linear.SchemeModuleOriginalTopExtClassIsoLaw
import all Linear.TildeActualCocycleModuleExt
import all Linear.TildeKoszulCoforkActualModuleExt
import all Linear.TildeKoszulCoforkAugmentationComparison
import all Linear.TildeKoszulNativeHomTopCohomology
import all Linear.TildeKoszulSourceInternalExtAcyclic
import all Linear.TildeNativeModuleExtMappedChain
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.AdditiveFunctorExtendComplex","Linear.AdditiveFunctorExtendNaturality","Linear.AdditiveFunctorExtendSingleCompatibility","Linear.AffineKoszulActualModuleExtInternalHomTop","Linear.AffineKoszulActualSheafExtTop","Linear.AffineKoszulDerivedModuleExtGeometricRestriction","Linear.AffineKoszulInternalHomCochain","Linear.AffineKoszulInternalHomComplexIso","Linear.AffineKoszulInternalHomTopCohomology","Linear.AffineKoszulOriginalSheafExtClass","Linear.ChainTopExtExactFunctorCompatibility","Linear.ChainTopExtExactFunctorMappedChain","Linear.CochainResolutionExactFunctorCompatibility","Linear.CochainResolutionExactFunctorObjects","Linear.CochainResolutionSourceIso","Linear.CochainResolutionTargetIso","Linear.KoszulExactTopExtCoefficientRestriction","Linear.KoszulExactTopExtCoefficients","Linear.KoszulNativeHomTopCohomology","Linear.KoszulNativeHomTopCokernel","Linear.MappedChainCokernelAugmentationSquare","Linear.MappedCochainTopCocycle","Linear.OriginalChainMappedAugmentationComparison","Linear.OriginalChainMappedExtComparison","Linear.OriginalChainMappedTopCocycle","Linear.OriginalChainTopExtTargetIso","Linear.ProjectiveResolutionOriginalChainClass","Linear.SchemeModuleAcyclicChainTopInternalExt","Linear.SchemeModuleAcyclicCokernelRankExt","Linear.SchemeModuleAcyclicCokernelTopInternalExt","Linear.SchemeModuleChainSourceAcyclic","Linear.SchemeModuleChainTopHomology","Linear.SchemeModuleOriginalTopExtClassIsoLaw","Linear.TildeActualCocycleModuleExt","Linear.TildeKoszulCoforkActualModuleExt","Linear.TildeKoszulCoforkAugmentationComparison","Linear.TildeKoszulNativeHomTopCohomology","Linear.TildeKoszulSourceInternalExtAcyclic","Linear.TildeNativeModuleExtMappedChain"]
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
