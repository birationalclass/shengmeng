module
import all Linear.AbstractLocalizedModuleResidueFiber
import all Linear.CoextensionReducedLocalFiberTrace
import all Linear.CoextensionTensorEvaluation
import all Linear.FiniteReducedFiberLocalFree
import all Linear.LocalizedCoextensionFiberPointTrace
import all Linear.LocalizedCoextensionReducedFiberTrace
import all Linear.LocalizedCoextensionResidueDual
import all Linear.LocalizedModuleResidueFiber
import all Linear.NativeCoextensionLocalizedTarget
import all Linear.PolynomialPointCoextensionTrace
import all Linear.RegularSequenceMaximalLocalization
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 50000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.AbstractLocalizedModuleResidueFiber","Linear.CoextensionReducedLocalFiberTrace","Linear.CoextensionTensorEvaluation","Linear.FiniteReducedFiberLocalFree","Linear.LocalizedCoextensionFiberPointTrace","Linear.LocalizedCoextensionReducedFiberTrace","Linear.LocalizedCoextensionResidueDual","Linear.LocalizedModuleResidueFiber","Linear.NativeCoextensionLocalizedTarget","Linear.PolynomialPointCoextensionTrace","Linear.RegularSequenceMaximalLocalization"]
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
