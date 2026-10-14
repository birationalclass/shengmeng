module
import all Linear.AffineFinitePresentationInternalHomQuasicoherent
import all Linear.AffineKoszulGeometricRestriction
import all Linear.AffineKoszulHomCoefficientRestriction
import all Linear.AffineKoszulTermInternalDualHom
import all Linear.AffinePushforwardGlobalSectionsNaturality
import all Linear.AffineQuasicoherentHomActualOpenEvaluation
import all Linear.AffineQuasicoherentHomActualOpenSections
import all Linear.AffineQuasicoherentHomOpenSections
import all Linear.AffineQuasicoherentSourceMorphisms
import all Linear.AffineTildeFinitePresentationHomIso
import all Linear.AffineTildeFinitePresentationInternalHom
import all Linear.AffineTildeHomPrecompositionValues
import all Linear.AffineTildeHomTargetNaturality
import all Linear.AffineTildePullbackExtendScalars
import all Linear.AffineTildePullbackUnit
import all Linear.AffineTildePullbackUnitValues
import all Linear.AffineTildeTensorPullback
import all Linear.AffineTildeTensorPullbackUnit
import all Linear.ExtendScalarsActualTensor
import all Linear.FinitePresentationHomCodomainLocalization
import all Linear.KoszulExactResolution
import all Linear.KoszulFunctionResolution
import all Linear.KoszulHomotopyTop
import all Linear.KoszulLocalGlobalExact
import all Linear.KoszulResolution
import all Linear.KoszulTop
import all Linear.KoszulTopComplementFunctional
import all Linear.KoszulTopHomCoefficientRestriction
import all Linear.LocalComplexExactReflection
import all Linear.LocalExactReflection
import all Linear.OriginalGlobalModuleScalar
import all Linear.SchemeModuleHomAffineChartSections
import all Linear.SchemeModuleHomEvaluationRestriction
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomOpenEvaluation
import all Linear.SchemeModuleHomOpenScalars
import all Linear.SchemeModuleHomPrecompose
import all Linear.SchemeModuleHomPrecomposeComparison
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleHomTopSections
import all Linear.SchemeModuleIsoPushforwardRestriction
import all Linear.TildeBasicOpenMono
import all Linear.TildeCoefficientQuotientGeometricPullback
import all Linear.TildeCoefficientQuotientGeometricUnit
import all Linear.TildeCoefficientQuotientPushforward
import all Linear.TildeCoefficientQuotientUnitValues
import all Linear.TildeComplexExact
import all Linear.TildeKoszulHomCoefficientRestriction
import all Linear.TildeKoszulPresentation
import all Linear.TildeKoszulStructureAugmentation
import all Linear.TildePreservesMono
import all Linear.TildePushforward
import all Linear.TildePushforwardUnitValues
import all Linear.TildeQuotientPushforward
import all Linear.Vendor.ExteriorBaseChange
import all Linear.Vendor.ExteriorProduct
import all Linear.Vendor.KoszulComplex
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
  if count <= 18 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
