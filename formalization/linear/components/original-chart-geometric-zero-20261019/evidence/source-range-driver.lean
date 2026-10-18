module
import all Linear.AffineKoszulGeometricClassZero
import all Linear.NativeKoszulMappedChartComplexIdentity
import all Linear.NativeProjectiveOpenKoszulExactChart
import all Linear.NativeProjectiveOpenKoszulExactChartObjects
import all Linear.ProjectivePulledOriginalChartDataCutStatement
import all Linear.ProjectivePulledOriginalChartDataCutZero
import all Linear.ProjectivePulledOriginalExactChartData
import all Linear.ProjectivePulledOriginalNamedExactChart
import all Linear.ProjectivePulledOriginalSetupChartCokernelLambdaZeroFamily
import all Linear.SchemeModuleChainOpenKoszulHomCokernel
import all Linear.SchemeModuleGeometricPullbackZero
import all Linear.SchemeModuleOpenKoszulChartData
import all Linear.SchemeModuleOpenKoszulChartDataCutZero
import all Linear.SchemeModuleOpenKoszulDataFromMappedPresentation
import all Linear.SchemeModuleOpenKoszulDataSourceEq
import all Linear.SchemeModuleOpenQuasicoherentCoefficientIso
import all Linear.SchemeModuleOriginalOpenKoszulCut
import all Linear.SchemeModuleOriginalOpenKoszulCutStatement
import all Linear.SchemeModuleOriginalOpenKoszulCutZero
import all Linear.SchemeModuleOriginalOpenKoszulQCCutStatement
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.AffineKoszulGeometricClassZero,`Linear.NativeKoszulMappedChartComplexIdentity,`Linear.NativeProjectiveOpenKoszulExactChart,`Linear.NativeProjectiveOpenKoszulExactChartObjects,`Linear.ProjectivePulledOriginalChartDataCutStatement,`Linear.ProjectivePulledOriginalChartDataCutZero,`Linear.ProjectivePulledOriginalExactChartData,`Linear.ProjectivePulledOriginalNamedExactChart,`Linear.ProjectivePulledOriginalSetupChartCokernelLambdaZeroFamily,`Linear.SchemeModuleChainOpenKoszulHomCokernel,`Linear.SchemeModuleGeometricPullbackZero,`Linear.SchemeModuleOpenKoszulChartData,`Linear.SchemeModuleOpenKoszulChartDataCutZero,`Linear.SchemeModuleOpenKoszulDataFromMappedPresentation,`Linear.SchemeModuleOpenKoszulDataSourceEq,`Linear.SchemeModuleOpenQuasicoherentCoefficientIso,`Linear.SchemeModuleOriginalOpenKoszulCut,`Linear.SchemeModuleOriginalOpenKoszulCutStatement,`Linear.SchemeModuleOriginalOpenKoszulCutZero,`Linear.SchemeModuleOriginalOpenKoszulQCCutStatement] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 35 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
