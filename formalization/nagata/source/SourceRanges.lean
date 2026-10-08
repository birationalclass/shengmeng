import OAI.AlgebraicGeometry.PlaneCurves.Nagata
import Lean.DeclarationRange
import Lean.Util.FoldConsts

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !modName.toString.startsWith "OAI.AlgebraicGeometry.PlaneCurves." then continue
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
