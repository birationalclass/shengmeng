module
import all Linear.PointedExactFunctorExtMap
import all Linear.PointedExactFunctorExtMapIsIso
import all Linear.PointedExactFunctorExtZero
import all Linear.SchemeModuleCohomologyPointedSource
import all Linear.SchemeModuleGlobalExtActualHCohomology
import all Linear.SchemeModuleGlobalExtActualHMap
import all Linear.SchemeModuleGlobalExtActualHZeroCalibration
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.PointedExactFunctorExtMap,`Linear.PointedExactFunctorExtMapIsIso,`Linear.PointedExactFunctorExtZero,`Linear.SchemeModuleCohomologyPointedSource,`Linear.SchemeModuleGlobalExtActualHCohomology,`Linear.SchemeModuleGlobalExtActualHMap,`Linear.SchemeModuleGlobalExtActualHZeroCalibration] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 18 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
