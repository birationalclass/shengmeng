module
import all Linear.NativeGeneralModuleHIntrinsicExactIso
import all Linear.NativeGeneralModuleHIntrinsicForget
import all Linear.NativeGeneralModuleHIntrinsicSpecForget
import all Linear.NativeGeneralModuleHIntrinsicSpecIso
import all Linear.NativeGeneralPublicHIntrinsicWitness
import all Linear.OriginalActualHBaseModuleForgetting
import all Linear.OriginalActualHSpecModuleObject
import all Linear.OriginalActualHSpecRestrictIso
import all Linear.OriginalModuleCatScalarMorphism
import all Linear.OriginalOrderedModuleHomologyScalarMorphism
import all Linear.OriginalScalarSquareModuleIso
import all Linear.OriginalScalarSquareModuleIsoLiteral
import all Linear.SchemeActualHRawObjectIdentity
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.NativeGeneralModuleHIntrinsicExactIso","Linear.NativeGeneralModuleHIntrinsicForget","Linear.NativeGeneralModuleHIntrinsicSpecForget","Linear.NativeGeneralModuleHIntrinsicSpecIso","Linear.NativeGeneralPublicHIntrinsicWitness","Linear.OriginalActualHBaseModuleForgetting","Linear.OriginalActualHSpecModuleObject","Linear.OriginalActualHSpecRestrictIso","Linear.OriginalModuleCatScalarMorphism","Linear.OriginalOrderedModuleHomologyScalarMorphism","Linear.OriginalScalarSquareModuleIso","Linear.OriginalScalarSquareModuleIsoLiteral","Linear.SchemeActualHRawObjectIdentity"]
  let isOwn := fun (n : Lean.Name) => match env.getModuleIdxFor? n with
    | none => false
    | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Linear."
  let mut count : Nat := 0
  let mut seen : Lean.NameSet := {}
  for i in [:env.header.moduleData.size] do
    let owner := env.header.moduleNames[i]!
    unless selected.contains owner.toString do continue
    let data := env.header.moduleData[i]!
    for name in data.constNames ++ data.extraConstNames do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | continue
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
