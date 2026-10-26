module
import all Linear.AffinePushforwardGlobalSectionsNaturality
import all Linear.AffineTildePullbackExtendScalars
import all Linear.AffineTildePullbackUnit
import all Linear.AffineTildePullbackUnitValues
import all Linear.AffineTildeTensorPullback
import all Linear.FiniteCutPrimeCoordinates
import all Linear.KoszulExactTopExtCoefficientRestriction
import all Linear.KoszulExactTopExtCoefficients
import all Linear.KoszulFunctionUnit
import all Linear.KoszulNativeCoextensionOriginalValues
import all Linear.KoszulOriginalModuleExtSheafValues
import all Linear.KoszulTopComplementFunctional
import all Linear.KoszulTopHomCoefficientRestriction
import all Linear.KoszulUnitExactness
import all Linear.OriginalCutEquationCoefficientModuleExtDual
import all Linear.OriginalCutEquationCoefficientModuleExtSheafDual
import all Linear.OriginalCutEquationCoefficientSheafDual
import all Linear.ProjectiveCutAffineKoszul
import all Linear.ProjectiveCutAllPrimeKoszul
import all Linear.ProjectiveCutOutsideExact
import all Linear.ProjectiveRegularCutOpen
import all Linear.TildePushforwardMappedUnitValues
import all Linear.TildePushforwardUnitValues
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.AffinePushforwardGlobalSectionsNaturality","Linear.AffineTildePullbackExtendScalars","Linear.AffineTildePullbackUnit","Linear.AffineTildePullbackUnitValues","Linear.AffineTildeTensorPullback","Linear.FiniteCutPrimeCoordinates","Linear.KoszulExactTopExtCoefficientRestriction","Linear.KoszulExactTopExtCoefficients","Linear.KoszulFunctionUnit","Linear.KoszulNativeCoextensionOriginalValues","Linear.KoszulOriginalModuleExtSheafValues","Linear.KoszulTopComplementFunctional","Linear.KoszulTopHomCoefficientRestriction","Linear.KoszulUnitExactness","Linear.OriginalCutEquationCoefficientModuleExtDual","Linear.OriginalCutEquationCoefficientModuleExtSheafDual","Linear.OriginalCutEquationCoefficientSheafDual","Linear.ProjectiveCutAffineKoszul","Linear.ProjectiveCutAllPrimeKoszul","Linear.ProjectiveCutOutsideExact","Linear.ProjectiveRegularCutOpen","Linear.TildePushforwardMappedUnitValues","Linear.TildePushforwardUnitValues"]
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
