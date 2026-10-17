module
import all Linear.AffineKoszulFramedHomCokernel
import all Linear.AffineKoszulHomGeometricCokernel
import all Linear.SchemeModuleHomArrowCokernel
import all Linear.SchemeModuleHomOpenImmersionBijective
import all Linear.SchemeModuleHomOpenImmersionCokernel
import all Linear.SchemeModuleHomOpenImmersionCokernelClass
import all Linear.SchemeModuleHomOpenImmersionCurry
import all Linear.SchemeModuleHomOpenImmersionIso
import all Linear.SchemeModuleHomOpenImmersionMorphism
import all Linear.SchemeModuleHomOpenImmersionRestriction
import all Linear.SchemeModuleHomOpenImmersionSourceNaturality
import all Linear.SchemeModuleHomTransportIso
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AffineKoszulFramedHomCokernel,`Linear.AffineKoszulHomGeometricCokernel,`Linear.SchemeModuleHomArrowCokernel,`Linear.SchemeModuleHomOpenImmersionBijective,`Linear.SchemeModuleHomOpenImmersionCokernel,`Linear.SchemeModuleHomOpenImmersionCokernelClass,`Linear.SchemeModuleHomOpenImmersionCurry,`Linear.SchemeModuleHomOpenImmersionIso,`Linear.SchemeModuleHomOpenImmersionMorphism,`Linear.SchemeModuleHomOpenImmersionRestriction,`Linear.SchemeModuleHomOpenImmersionSourceNaturality,`Linear.SchemeModuleHomTransportIso] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count != 23 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
