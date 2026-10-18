module
import all Linear.NativeKoszulTargetOffCutZero
import all Linear.ParameterFamilyEnrichSharedFacts
import all Linear.ProjectivePulledOriginalChartInternalExtSupport
import all Linear.ProjectivePulledOriginalGlobalGeometricZero
import all Linear.ProjectivePulledOriginalNamedChartImage
import all Linear.ProjectivePulledOriginalNamedChartObjects
import all Linear.ProjectivePulledOriginalNativeCokernelIso
import all Linear.ProjectivePulledOriginalSetupGlobalGeometricZeroFamily
import all Linear.ProjectivePulledOriginalTargetOffCutZero
import all Linear.SchemeModuleChartImageHEq
import all Linear.SchemeModuleChartInternalExtCover
import all Linear.SchemeModuleChartInternalExtSupport
import all Linear.SchemeModuleGlobalExtOpenZero
import all Linear.SchemeModuleGlobalGeometricZeroCokernel
import all Linear.SchemeModuleInternalExtOpenSupport
import all Linear.SchemeModuleInternalExtSupportedUnit
import all Linear.SchemeModuleOpenKoszulChartDataGlobalZero
import all Linear.SchemeModuleRestrictionUnitHEq
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.NativeKoszulTargetOffCutZero,`Linear.ParameterFamilyEnrichSharedFacts,`Linear.ProjectivePulledOriginalChartInternalExtSupport,`Linear.ProjectivePulledOriginalGlobalGeometricZero,`Linear.ProjectivePulledOriginalNamedChartImage,`Linear.ProjectivePulledOriginalNamedChartObjects,`Linear.ProjectivePulledOriginalNativeCokernelIso,`Linear.ProjectivePulledOriginalSetupGlobalGeometricZeroFamily,`Linear.ProjectivePulledOriginalTargetOffCutZero,`Linear.SchemeModuleChartImageHEq,`Linear.SchemeModuleChartInternalExtCover,`Linear.SchemeModuleChartInternalExtSupport,`Linear.SchemeModuleGlobalExtOpenZero,`Linear.SchemeModuleGlobalGeometricZeroCokernel,`Linear.SchemeModuleInternalExtOpenSupport,`Linear.SchemeModuleInternalExtSupportedUnit,`Linear.SchemeModuleOpenKoszulChartDataGlobalZero,`Linear.SchemeModuleRestrictionUnitHEq] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 26 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
