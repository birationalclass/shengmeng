module
import all Linear.NativeKoszulTargetOffCutZero
import all Linear.ParameterFamilyProjectSharedWitness
import all Linear.ProjectivePulledOriginalChartInternalExtSupport
import all Linear.ProjectivePulledOriginalGlobalIntrinsicZero
import all Linear.ProjectivePulledOriginalNamedChartImage
import all Linear.ProjectivePulledOriginalNamedChartObjects
import all Linear.ProjectivePulledOriginalNativeCokernelIso
import all Linear.ProjectivePulledOriginalSetupGlobalIntrinsicFamily
import all Linear.ProjectivePulledOriginalTargetOffCutZero
import all Linear.SchemeModuleChartImageHEq
import all Linear.SchemeModuleChartInternalExtCover
import all Linear.SchemeModuleChartInternalExtSupport
import all Linear.SchemeModuleGlobalExtOpenZero
import all Linear.SchemeModuleGlobalKoszulIntrinsicZero
import all Linear.SchemeModuleInternalExtOpenSupport
import all Linear.SchemeModuleInternalExtSupportedUnit
import all Linear.SchemeModuleRestrictionUnitHEq
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeKoszulTargetOffCutZero","Linear.ParameterFamilyProjectSharedWitness","Linear.ProjectivePulledOriginalChartInternalExtSupport","Linear.ProjectivePulledOriginalGlobalIntrinsicZero","Linear.ProjectivePulledOriginalNamedChartImage","Linear.ProjectivePulledOriginalNamedChartObjects","Linear.ProjectivePulledOriginalNativeCokernelIso","Linear.ProjectivePulledOriginalSetupGlobalIntrinsicFamily","Linear.ProjectivePulledOriginalTargetOffCutZero","Linear.SchemeModuleChartImageHEq","Linear.SchemeModuleChartInternalExtCover","Linear.SchemeModuleChartInternalExtSupport","Linear.SchemeModuleGlobalExtOpenZero","Linear.SchemeModuleGlobalKoszulIntrinsicZero","Linear.SchemeModuleInternalExtOpenSupport","Linear.SchemeModuleInternalExtSupportedUnit","Linear.SchemeModuleRestrictionUnitHEq"]
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
