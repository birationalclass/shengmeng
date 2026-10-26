module
import all Linear.SchemeModuleHomGlobal
import all Linear.SchemeModuleHomModuleSections
import all Linear.SchemeModuleHomModuleSheaf
import all Linear.SchemeModuleHomPresheaf
import all Linear.SchemeModuleHomRestriction
import all Linear.SchemeModuleHomScalar
import all Linear.SchemeModuleHomSheaf
import all Linear.SchemeModuleHomTopSections
import all Linear.SchemeModuleInjectiveActualCohomology
import all Linear.SchemeModuleInjectiveFlasque
import all Linear.SchemeModuleIsoRestrictionEquivalence
import all Linear.SchemeModuleOpenRestrictionActualAbelian
import all Linear.SchemeModuleOpenRestrictionExact
import all Linear.SchemeModuleScalarNaturality
import all Linear.SchemeModuleSchemeIsoGlobalExt
import all Linear.SchemeModuleSpecChartSections
import all Linear.SchemeModuleSpecOpenNamedScalar
import all Linear.SchemeModuleSpecOpenSections
import all Linear.SchemeModuleSpecOpenSectionsRestrictedScalar
import all Linear.SchemeModuleSpecOpenSectionsScalar
import all Linear.SchemeModuleUnitHomSections
import all Linear.SemilinearComparisonScalar
import all Linear.SheafEmbeddingSectionTransport
import all Linear.SheafFreePresentationOfExact
import all Linear.SheafFreePresentationOfExactFinite
import all Linear.SoclePairing
import all Linear.SocleTransport
import all Linear.Target
import all Linear.TensorDifference
import all Linear.TensorSpecialization
import all Linear.TildeBasicOpenMono
import all Linear.TildePreservesMono
import all Linear.TopAbelianSheafFlasqueCohomology
import all Linear.TopAbelianSheafFlasqueShortExact
import all Linear.TopAbelianSheafInjectiveFlasque
import all Linear.TopAbelianSheafIntegerSections
import all Linear.TopCechFiniteFreeSheafTerms
import all Linear.TopCechFreePresheafSimplicialIso
import all Linear.TopCechFreeSheafResolution
import all Linear.TopCechIntegerTarget
import all Linear.TopCechLocalAcyclicTerms
import all Linear.TopCoverGeneratedTerminalSheaf
import all Linear.TopDeterminant
import all Linear.TopFormalFreePresheafValueHom
import all Linear.TopFreePresheafHomSheafCoefficient
import all Linear.TopOpenAbelianSheafRestriction
import all Linear.TopOpenFreeAbelianHomPresheaf
import all Linear.TopOpenFreeAbelianSheaf
import all Linear.TopOpenFreeAbelianSheafAddSections
import all Linear.TopOpenFreeAbelianSheafSections
import all Linear.TopOpenFreeAbelianSheafSectionsNaturality
import all Linear.TopOpenRestrictionActualCohomology
import all Linear.TopOpenRestrictionHomSections
import all Linear.TopOpenRestrictionPointedSource
import all Linear.TraceElement
import all Linear.UniversalDifference
import all Linear.VectorDualCokernelKernel
import all Linear.Vendor.ExteriorBaseChange
import all Linear.Vendor.ExteriorProduct
import all Linear.Vendor.KoszulComplex
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.SchemeModuleHomGlobal","Linear.SchemeModuleHomModuleSections","Linear.SchemeModuleHomModuleSheaf","Linear.SchemeModuleHomPresheaf","Linear.SchemeModuleHomRestriction","Linear.SchemeModuleHomScalar","Linear.SchemeModuleHomSheaf","Linear.SchemeModuleHomTopSections","Linear.SchemeModuleInjectiveActualCohomology","Linear.SchemeModuleInjectiveFlasque","Linear.SchemeModuleIsoRestrictionEquivalence","Linear.SchemeModuleOpenRestrictionActualAbelian","Linear.SchemeModuleOpenRestrictionExact","Linear.SchemeModuleScalarNaturality","Linear.SchemeModuleSchemeIsoGlobalExt","Linear.SchemeModuleSpecChartSections","Linear.SchemeModuleSpecOpenNamedScalar","Linear.SchemeModuleSpecOpenSections","Linear.SchemeModuleSpecOpenSectionsRestrictedScalar","Linear.SchemeModuleSpecOpenSectionsScalar","Linear.SchemeModuleUnitHomSections","Linear.SemilinearComparisonScalar","Linear.SheafEmbeddingSectionTransport","Linear.SheafFreePresentationOfExact","Linear.SheafFreePresentationOfExactFinite","Linear.SoclePairing","Linear.SocleTransport","Linear.Target","Linear.TensorDifference","Linear.TensorSpecialization","Linear.TildeBasicOpenMono","Linear.TildePreservesMono","Linear.TopAbelianSheafFlasqueCohomology","Linear.TopAbelianSheafFlasqueShortExact","Linear.TopAbelianSheafInjectiveFlasque","Linear.TopAbelianSheafIntegerSections","Linear.TopCechFiniteFreeSheafTerms","Linear.TopCechFreePresheafSimplicialIso","Linear.TopCechFreeSheafResolution","Linear.TopCechIntegerTarget","Linear.TopCechLocalAcyclicTerms","Linear.TopCoverGeneratedTerminalSheaf","Linear.TopDeterminant","Linear.TopFormalFreePresheafValueHom","Linear.TopFreePresheafHomSheafCoefficient","Linear.TopOpenAbelianSheafRestriction","Linear.TopOpenFreeAbelianHomPresheaf","Linear.TopOpenFreeAbelianSheaf","Linear.TopOpenFreeAbelianSheafAddSections","Linear.TopOpenFreeAbelianSheafSections","Linear.TopOpenFreeAbelianSheafSectionsNaturality","Linear.TopOpenRestrictionActualCohomology","Linear.TopOpenRestrictionHomSections","Linear.TopOpenRestrictionPointedSource","Linear.TraceElement","Linear.UniversalDifference","Linear.VectorDualCokernelKernel","Linear.Vendor.ExteriorBaseChange","Linear.Vendor.ExteriorProduct","Linear.Vendor.KoszulComplex"]
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
