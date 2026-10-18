module
import all Linear.ActualAbelianSheafConstantPullback
import all Linear.ClosedDiscreteSupportSheafFlasque
import all Linear.DiscreteClosedMapSupportFlasque
import all Linear.DiscreteSheafCohomology
import all Linear.DiscreteSheafFlasque
import all Linear.DiscreteSheafPushforwardCohomology
import all Linear.DiscreteSheafPushforwardExact
import all Linear.DiscreteSheafSectionsExact
import all Linear.FiniteCutArtinianTopology
import all Linear.InjectiveCocycleExtPresentation
import all Linear.InjectiveCocycleTransport
import all Linear.SchemeModuleAdditiveSheafColimits
import all Linear.SchemeModuleCanonicalGlobalToInternalExt
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExt
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections
import all Linear.SchemeModuleDerivedInternalHom
import all Linear.SchemeModuleFiniteSupportCohomology
import all Linear.SchemeModuleFlasqueKernelSectionLifting
import all Linear.SchemeModuleGlobalSectionMorphism
import all Linear.SchemeModuleGlobalToInternalExt
import all Linear.SchemeModuleGlobalToInternalExtCocycle
import all Linear.SchemeModuleGlobalToInternalExtNaturality
import all Linear.SchemeModuleHomEvaluationRestriction
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomOpenImmersionBijective
import all Linear.SchemeModuleHomOpenImmersionIso
import all Linear.SchemeModuleHomOpenImmersionMorphism
import all Linear.SchemeModuleHomOpenImmersionRestriction
import all Linear.SchemeModuleHomPostcompose
import all Linear.SchemeModuleHomPostcomposeSection
import all Linear.SchemeModuleHomPrecompose
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleHomUnitCurry
import all Linear.SchemeModuleHomZeroSourceSupport
import all Linear.SchemeModuleInjectiveInternalHomCycleSurjective
import all Linear.SchemeModuleInjectiveInternalHomCycles
import all Linear.SchemeModuleInjectiveInternalHomNaturality
import all Linear.SchemeModuleInternalHomCoefficientFunctor
import all Linear.SchemeModuleInternalHomComplex
import all Linear.SchemeModuleIsoOnActualCover
import all Linear.SchemeModuleOpenRestrictionExact
import all Linear.SchemeModulePushforwardOpenSupport
import all Linear.SchemeModuleSupportedInternalHomClass
import all Linear.SchemeModuleSupportedRestrictionUnit
import all Linear.SchemeModuleSupportedSubHomFlasque
import all Linear.SchemeModuleSupportedUnitHomLifting
import all Linear.SheafEmbeddingSectionTransport
import Lean.DeclarationRange
import Lean.Util.FoldConsts
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if !([`Linear.ActualAbelianSheafConstantPullback,`Linear.ClosedDiscreteSupportSheafFlasque,`Linear.DiscreteClosedMapSupportFlasque,`Linear.DiscreteSheafCohomology,`Linear.DiscreteSheafFlasque,`Linear.DiscreteSheafPushforwardCohomology,`Linear.DiscreteSheafPushforwardExact,`Linear.DiscreteSheafSectionsExact,`Linear.FiniteCutArtinianTopology,`Linear.InjectiveCocycleExtPresentation,`Linear.InjectiveCocycleTransport,`Linear.SchemeModuleAdditiveSheafColimits,`Linear.SchemeModuleCanonicalGlobalToInternalExt,`Linear.SchemeModuleClosedDiscreteGlobalToInternalExt,`Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections,`Linear.SchemeModuleDerivedInternalHom,`Linear.SchemeModuleFiniteSupportCohomology,`Linear.SchemeModuleFlasqueKernelSectionLifting,`Linear.SchemeModuleGlobalSectionMorphism,`Linear.SchemeModuleGlobalToInternalExt,`Linear.SchemeModuleGlobalToInternalExtCocycle,`Linear.SchemeModuleGlobalToInternalExtNaturality,`Linear.SchemeModuleHomEvaluationRestriction,`Linear.SchemeModuleHomGlobal,`Linear.SchemeModuleHomModuleSections,`Linear.SchemeModuleHomModuleSheaf,`Linear.SchemeModuleHomOpenImmersionBijective,`Linear.SchemeModuleHomOpenImmersionIso,`Linear.SchemeModuleHomOpenImmersionMorphism,`Linear.SchemeModuleHomOpenImmersionRestriction,`Linear.SchemeModuleHomPostcompose,`Linear.SchemeModuleHomPostcomposeSection,`Linear.SchemeModuleHomPrecompose,`Linear.SchemeModuleHomPresheaf,`Linear.SchemeModuleHomRestriction,`Linear.SchemeModuleHomScalar,`Linear.SchemeModuleHomSheaf,`Linear.SchemeModuleHomUnitCurry,`Linear.SchemeModuleHomZeroSourceSupport,`Linear.SchemeModuleInjectiveInternalHomCycleSurjective,`Linear.SchemeModuleInjectiveInternalHomCycles,`Linear.SchemeModuleInjectiveInternalHomNaturality,`Linear.SchemeModuleInternalHomCoefficientFunctor,`Linear.SchemeModuleInternalHomComplex,`Linear.SchemeModuleIsoOnActualCover,`Linear.SchemeModuleOpenRestrictionExact,`Linear.SchemeModulePushforwardOpenSupport,`Linear.SchemeModuleSupportedInternalHomClass,`Linear.SchemeModuleSupportedRestrictionUnit,`Linear.SchemeModuleSupportedSubHomFlasque,`Linear.SchemeModuleSupportedUnitHomLifting,`Linear.SheafEmbeddingSectionTransport] : List Lean.Name).contains modName then continue
    let deps := String.intercalate "," (info.getUsedConstantsAsSet.toArray.toList.map toString)
    Lean.logInfo m!"SOURCE_DEPENDENCIES|{name}|{modName}|{deps}"
    let some ranges ← Lean.findDeclarationRanges? name | continue
    let r := ranges.range
    Lean.logInfo m!"SOURCE_RANGE|{name}|{modName}|{r.pos.line}|{r.pos.column}|{r.endPos.line}|{r.endPos.column}|{deps}"
    count := count + 1
  if count < 25 then throwError "Transitive project declaration ranges are missing"
  Lean.logInfo m!"SOURCE_RANGE_COUNT|{count}"
