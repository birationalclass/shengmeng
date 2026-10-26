module
import all Linear.HomogeneousConeAffineFinite
import all Linear.HomogeneousCutAffineFinite
import all Linear.HomogeneousNoBasePointFinite
import all Linear.HomogeneousQuotientMapFinite
import all Linear.HomogeneousQuotientRelation
import all Linear.OriginalCutEquationZeroFiber
import all Linear.ProjectiveAffineMaximalPoint
import all Linear.ProjectiveCutEquationFiberLocalData
import all Linear.ProjectiveCutEquationMapFinite
import all Linear.ProjectiveCutEquationPointTrace
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.HomogeneousConeAffineFinite","Linear.HomogeneousCutAffineFinite","Linear.HomogeneousNoBasePointFinite","Linear.HomogeneousQuotientMapFinite","Linear.HomogeneousQuotientRelation","Linear.OriginalCutEquationZeroFiber","Linear.ProjectiveAffineMaximalPoint","Linear.ProjectiveCutEquationFiberLocalData","Linear.ProjectiveCutEquationMapFinite","Linear.ProjectiveCutEquationPointTrace"]
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
