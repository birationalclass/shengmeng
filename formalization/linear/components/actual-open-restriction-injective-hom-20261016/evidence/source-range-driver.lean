module
import all Linear.OverOpenInjectiveRestriction
import all Linear.OverOpenZeroPresheaf
import all Linear.OverOpenZeroPresheafAdjunction
import all Linear.OverOpenZeroPresheafFunctor
import all Linear.OverOpenZeroSheafAdjunction
import all Linear.OverOpenZeroSheafFunctor
import all Linear.SchemeModuleHomEvaluationRestriction
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomPostcompose
import all Linear.SchemeModuleHomPostcomposeSection
import all Linear.SchemeModuleHomPrecompose
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleInjectiveHomEpi
import all Linear.SchemeModuleInjectiveHomExact
import all Linear.SchemeModuleInternalHomBifunctor
import all Linear.SchemeModuleInternalHomCoefficientFunctor
import all Linear.SchemeModuleInternalHomCoefficientLimits
import all Linear.SchemeModuleInternalHomComplex
import all Linear.SchemeModuleInternalHomSourceLimits
import all Linear.SchemeModuleOpenInjectives
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !modName.toString.startsWith "Linear." && modName != `Linear then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count <= 15 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
