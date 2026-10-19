module
import all Linear.AlternatingHomOppositeComplex
import all Linear.FormalCoproductContravariantEvaluation
import all Linear.InjectiveHomResolutionAcyclic
import all Linear.TopCechFreePresheafSimplicialIso
import all Linear.TopCechFreeSheafHomComplex
import all Linear.TopFreePresheafHomSheafCoefficient
import all Linear.TopInjectiveAbelianSheafCechAcyclic
import all Linear.TopOpenFreeAbelianHomPresheaf
import all Linear.TopOpenFreeAbelianSheafAddSections
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AlternatingHomOppositeComplex,`Linear.FormalCoproductContravariantEvaluation,`Linear.InjectiveHomResolutionAcyclic,`Linear.TopCechFreePresheafSimplicialIso,`Linear.TopCechFreeSheafHomComplex,`Linear.TopFreePresheafHomSheafCoefficient,`Linear.TopInjectiveAbelianSheafCechAcyclic,`Linear.TopOpenFreeAbelianHomPresheaf,`Linear.TopOpenFreeAbelianSheafAddSections] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 17 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
