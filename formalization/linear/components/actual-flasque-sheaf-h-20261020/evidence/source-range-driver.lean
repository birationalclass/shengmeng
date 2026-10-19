module
import all Linear.ExtZeroHomCoefficientNaturality
import all Linear.SchemeModuleGlobalExtActualHZero
import all Linear.SchemeModuleInjectiveActualCohomology
import all Linear.TopAbelianSheafFlasqueCohomology
import all Linear.TopAbelianSheafFlasqueShortExact
import all Linear.TopAbelianSheafInjectiveFlasque
import all Linear.TopAbelianSheafIntegerSections
import all Linear.TopOpenFreeAbelianSheaf
import all Linear.TopOpenFreeAbelianSheafSections
import all Linear.TopOpenFreeAbelianSheafSectionsNaturality
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.ExtZeroHomCoefficientNaturality,`Linear.SchemeModuleGlobalExtActualHZero,`Linear.SchemeModuleInjectiveActualCohomology,`Linear.TopAbelianSheafFlasqueCohomology,`Linear.TopAbelianSheafFlasqueShortExact,`Linear.TopAbelianSheafInjectiveFlasque,`Linear.TopAbelianSheafIntegerSections,`Linear.TopOpenFreeAbelianSheaf,`Linear.TopOpenFreeAbelianSheafSections,`Linear.TopOpenFreeAbelianSheafSectionsNaturality] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 20 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
