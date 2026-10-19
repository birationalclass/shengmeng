module
import all Linear.AdjunctionCounitHomEquiv
import all Linear.InjectiveClosedClassExtAcyclic
import all Linear.ModuleSheafificationCounitHomEquiv
import all Linear.OverOpenInjectiveUnitExtension
import all Linear.OverOpenUnitZeroPresheafMono
import all Linear.OverOpenUnitZeroSheafAdjoint
import all Linear.OverOpenUnitZeroSheafBinding
import all Linear.OverOpenUnitZeroSheafMono
import all Linear.SchemeModuleFlasqueExtAcyclic
import all Linear.SchemeModuleFlasqueShortExact
import all Linear.SchemeModuleInjectiveFlasque
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AdjunctionCounitHomEquiv,`Linear.InjectiveClosedClassExtAcyclic,`Linear.ModuleSheafificationCounitHomEquiv,`Linear.OverOpenInjectiveUnitExtension,`Linear.OverOpenUnitZeroPresheafMono,`Linear.OverOpenUnitZeroSheafAdjoint,`Linear.OverOpenUnitZeroSheafBinding,`Linear.OverOpenUnitZeroSheafMono,`Linear.SchemeModuleFlasqueExtAcyclic,`Linear.SchemeModuleFlasqueShortExact,`Linear.SchemeModuleInjectiveFlasque] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 21 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
