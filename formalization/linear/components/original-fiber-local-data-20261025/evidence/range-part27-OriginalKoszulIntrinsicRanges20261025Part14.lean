module
import all Linear.TargetGoodLoci
import all Linear.TargetLinearNormal
import all Linear.TensorDifference
import all Linear.TensorSpecialization
import all Linear.TildeBasicOpenMono
import all Linear.TildeCoefficientQuotientGeometricPullback
import all Linear.TildeCoefficientQuotientGeometricUnit
import all Linear.TildeCoefficientQuotientPushforward
import all Linear.TildeCoefficientQuotientUnitValues
import all Linear.TildeComplexExact
import all Linear.TildeKoszulHomCoefficientRestriction
import all Linear.TildeKoszulOriginalCutCofork
import all Linear.TildeKoszulPresentation
import all Linear.TildeKoszulStructureAugmentation
import all Linear.TildePreservesMono
import all Linear.TildePushforward
import all Linear.TildePushforwardUnitValues
import all Linear.TildeQuotientPushforward
import all Linear.TopDeterminant
import all Linear.TraceElement
import all Linear.UniversalDifference
import all Linear.UnramifiedEvaluationQuotient
import all Linear.UnramifiedLocalRingHom
import all Linear.UnramifiedParameters
import all Linear.Vendor.CM.CohenMacaulayBasic
import all Linear.Vendor.CM.CohenMacaulayCatenary
import all Linear.Vendor.CM.CohenMacaulayPolynomial
import all Linear.Vendor.CM.DepthBasic
import all Linear.Vendor.CM.DepthIschebeck
import all Linear.Vendor.ExteriorBaseChange
import all Linear.Vendor.ExteriorProduct
import all Linear.Vendor.KoszulComplex
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.TargetGoodLoci","Linear.TargetLinearNormal","Linear.TensorDifference","Linear.TensorSpecialization","Linear.TildeBasicOpenMono","Linear.TildeCoefficientQuotientGeometricPullback","Linear.TildeCoefficientQuotientGeometricUnit","Linear.TildeCoefficientQuotientPushforward","Linear.TildeCoefficientQuotientUnitValues","Linear.TildeComplexExact","Linear.TildeKoszulHomCoefficientRestriction","Linear.TildeKoszulOriginalCutCofork","Linear.TildeKoszulPresentation","Linear.TildeKoszulStructureAugmentation","Linear.TildePreservesMono","Linear.TildePushforward","Linear.TildePushforwardUnitValues","Linear.TildeQuotientPushforward","Linear.TopDeterminant","Linear.TraceElement","Linear.UniversalDifference","Linear.UnramifiedEvaluationQuotient","Linear.UnramifiedLocalRingHom","Linear.UnramifiedParameters","Linear.Vendor.CM.CohenMacaulayBasic","Linear.Vendor.CM.CohenMacaulayCatenary","Linear.Vendor.CM.CohenMacaulayPolynomial","Linear.Vendor.CM.DepthBasic","Linear.Vendor.CM.DepthIschebeck","Linear.Vendor.ExteriorBaseChange","Linear.Vendor.ExteriorProduct","Linear.Vendor.KoszulComplex"]
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
