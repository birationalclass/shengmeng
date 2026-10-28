module
import all Linear.CategoricalIsoTransHomEquality
import all Linear.CategoricalOriginalSquareRefold
import all Linear.CheckedSingleUnfoldIdentity
import all Linear.ConcreteOriginalScalarSquareApply
import all Linear.ConcreteOriginalScalarSquareExt
import all Linear.NativeGeneralModuleHFactorizationHom
import all Linear.NativeGeneralModuleHScalarCompositeProof
import all Linear.NativeGeneralModuleHScalarPointwiseProof
import all Linear.NativeGeneralModuleHScalarProof
import all Linear.NativeGeneralPublicHFactorizationCompositeHom
import all Linear.NativeGeneralPublicHScalarCompositeProof
import all Linear.NativeGeneralPublicHScalarCompositeTheorem
import all Linear.NativeGeneralPublicHScalarExplicitProof
import all Linear.NativeGeneralPublicHScalarTheorem
import all Linear.NativePublicHScalarOperatorIdentity
import all Linear.NativePublicHScalarOperatorPointwiseProof
import all Linear.NativeSourceContextHScalarValueProof
import all Linear.NativeSourcePublicHComparisonPointwiseProof
import all Linear.NativeSourcePublicHScalarPointwiseProof
import all Linear.NativeSourcePublicHScalarSquareExtProof
import all Linear.NativeSourcePublicHScalarTheorem
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.CategoricalIsoTransHomEquality","Linear.CategoricalOriginalSquareRefold","Linear.CheckedSingleUnfoldIdentity","Linear.ConcreteOriginalScalarSquareApply","Linear.ConcreteOriginalScalarSquareExt","Linear.NativeGeneralModuleHFactorizationHom","Linear.NativeGeneralModuleHScalarCompositeProof","Linear.NativeGeneralModuleHScalarPointwiseProof","Linear.NativeGeneralModuleHScalarProof","Linear.NativeGeneralPublicHFactorizationCompositeHom","Linear.NativeGeneralPublicHScalarCompositeProof","Linear.NativeGeneralPublicHScalarCompositeTheorem","Linear.NativeGeneralPublicHScalarExplicitProof","Linear.NativeGeneralPublicHScalarTheorem","Linear.NativePublicHScalarOperatorIdentity","Linear.NativePublicHScalarOperatorPointwiseProof","Linear.NativeSourceContextHScalarValueProof","Linear.NativeSourcePublicHComparisonPointwiseProof","Linear.NativeSourcePublicHScalarPointwiseProof","Linear.NativeSourcePublicHScalarSquareExtProof","Linear.NativeSourcePublicHScalarTheorem"]
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
