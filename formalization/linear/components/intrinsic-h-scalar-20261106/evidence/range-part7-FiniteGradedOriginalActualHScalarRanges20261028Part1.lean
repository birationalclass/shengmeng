module
import all Linear.CategoricalIsoHomFactorization
import all Linear.CategoricalMorphismFactorizationEquality
import all Linear.CategoricalScalarSquareComposition
import all Linear.CheckedEqualityRightCache
import all Linear.CheckedFoldEqualityRight
import all Linear.CheckedFoldSquareRight
import all Linear.CheckedOpaqueProof
import all Linear.CheckedScalarMapCache
import all Linear.CheckedSquareComparisonCache
import all Linear.CheckedSquarePublicCodomain
import all Linear.CheckedSquareTargetContext
import all Linear.NativeFiniteGradedSourceActualHScalarProof
import all Linear.NativeGeneralActualHOriginalScalar
import all Linear.NativeGeneralActualHOriginalScalarComposite
import all Linear.NativeGeneralPublicHAtomicIdentities
import all Linear.NativeGeneralPublicHComparisonCalibration
import all Linear.NativeGeneralPublicHComparisonHomCalibration
import all Linear.NativeGeneralPublicHFactorizationHom
import all Linear.NativeGeneralSourcePublicHCalibration
import all Linear.NativeOriginalHScalarCachedOperator
import all Linear.NativeProjectiveOriginalHScalarObjects
import all Linear.NativeSourceActualHCachedComparisonScalar
import all Linear.NativeSourceActualHCachedIdentity
import all Linear.NativeSourceActualHCachedRightScalar
import all Linear.NativeSourceActualHContextScalarSquare
import all Linear.NativeSourceActualHRawScalarTheorem
import all Linear.NativeSourcePublicHComparisonHomCalibration
import all Linear.NativeSourcePublicHComparisonHomIdentity
import all Linear.NativeSourcePublicHComparisonTypedHom
import all Linear.NativeSourcePublicHScalarOperator
import all Linear.SchemeModuleActualCohomologyGroup
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.CategoricalIsoHomFactorization","Linear.CategoricalMorphismFactorizationEquality","Linear.CategoricalScalarSquareComposition","Linear.CheckedEqualityRightCache","Linear.CheckedFoldEqualityRight","Linear.CheckedFoldSquareRight","Linear.CheckedOpaqueProof","Linear.CheckedScalarMapCache","Linear.CheckedSquareComparisonCache","Linear.CheckedSquarePublicCodomain","Linear.CheckedSquareTargetContext","Linear.NativeFiniteGradedSourceActualHScalarProof","Linear.NativeGeneralActualHOriginalScalar","Linear.NativeGeneralActualHOriginalScalarComposite","Linear.NativeGeneralPublicHAtomicIdentities","Linear.NativeGeneralPublicHComparisonCalibration","Linear.NativeGeneralPublicHComparisonHomCalibration","Linear.NativeGeneralPublicHFactorizationHom","Linear.NativeGeneralSourcePublicHCalibration","Linear.NativeOriginalHScalarCachedOperator","Linear.NativeProjectiveOriginalHScalarObjects","Linear.NativeSourceActualHCachedComparisonScalar","Linear.NativeSourceActualHCachedIdentity","Linear.NativeSourceActualHCachedRightScalar","Linear.NativeSourceActualHContextScalarSquare","Linear.NativeSourceActualHRawScalarTheorem","Linear.NativeSourcePublicHComparisonHomCalibration","Linear.NativeSourcePublicHComparisonHomIdentity","Linear.NativeSourcePublicHComparisonTypedHom","Linear.NativeSourcePublicHScalarOperator","Linear.SchemeModuleActualCohomologyGroup"]
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
