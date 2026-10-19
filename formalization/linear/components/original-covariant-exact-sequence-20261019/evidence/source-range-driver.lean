module
import all Linear.CochainActualRoofCovariantExact
import all Linear.CochainActualTopCovariantExact
import all Linear.CochainOpcycleSignedExact
import all Linear.CochainOpcycleSignedExtension
import all Linear.CochainOpcycleSignedRoof
import all Linear.CochainOpcycleUnsignedExact
import all Linear.CochainOpcycleUnsignedExtension
import all Linear.ExtUnitSmulComposition
import all Linear.IteratedCovariantExtClass
import all Linear.IteratedCovariantExtExact
import all Linear.IteratedCovariantExtInjective
import all Linear.IteratedCovariantExtSurjective
import all Linear.OriginalChainCovariantCoefficientIso
import all Linear.OriginalChainCovariantExact
import all Linear.ProjectivePulledOriginalCovariantExact
import all Linear.RelativeAcyclicCovariantBoundary
import all Linear.SchemeModuleOriginalCovariantExact
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.CochainActualRoofCovariantExact,`Linear.CochainActualTopCovariantExact,`Linear.CochainOpcycleSignedExact,`Linear.CochainOpcycleSignedExtension,`Linear.CochainOpcycleSignedRoof,`Linear.CochainOpcycleUnsignedExact,`Linear.CochainOpcycleUnsignedExtension,`Linear.ExtUnitSmulComposition,`Linear.IteratedCovariantExtClass,`Linear.IteratedCovariantExtExact,`Linear.IteratedCovariantExtInjective,`Linear.IteratedCovariantExtSurjective,`Linear.OriginalChainCovariantCoefficientIso,`Linear.OriginalChainCovariantExact,`Linear.ProjectivePulledOriginalCovariantExact,`Linear.RelativeAcyclicCovariantBoundary,`Linear.SchemeModuleOriginalCovariantExact] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 41 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
