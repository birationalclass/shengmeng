module
import all Linear.AcyclicChainExtVanishing
import all Linear.AcyclicChainHomExtension
import all Linear.AcyclicChainOpcycleSequence
import all Linear.AcyclicResolutionExtVanishing
import all Linear.FiniteCoproductExtAcyclic
import all Linear.PointedExactFunctorExtZeroHomEquiv
import all Linear.TopCechFiniteFreeSheafTerms
import all Linear.TopCechLocalAcyclicTerms
import all Linear.TopCechNativeHVanishingCriterion
import all Linear.TopOpenAbelianSheafRestriction
import all Linear.TopOpenRestrictionActualCohomology
import all Linear.TopOpenRestrictionHomSections
import all Linear.TopOpenRestrictionPointedSource
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AcyclicChainExtVanishing,`Linear.AcyclicChainHomExtension,`Linear.AcyclicChainOpcycleSequence,`Linear.AcyclicResolutionExtVanishing,`Linear.FiniteCoproductExtAcyclic,`Linear.PointedExactFunctorExtZeroHomEquiv,`Linear.TopCechFiniteFreeSheafTerms,`Linear.TopCechLocalAcyclicTerms,`Linear.TopCechNativeHVanishingCriterion,`Linear.TopOpenAbelianSheafRestriction,`Linear.TopOpenRestrictionActualCohomology,`Linear.TopOpenRestrictionHomSections,`Linear.TopOpenRestrictionPointedSource] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 28 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
