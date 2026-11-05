module
import all Linear.AdditiveFunctorEndRingHom
import all Linear.AdditiveFunctorScalarSquare
import all Linear.NativeOriginalPublicScalarIntrinsic
import all Linear.NativeOriginalRawScalarIntrinsicPieces
import all Linear.NativeOriginalScalarEndPackageCalibration
import all Linear.NativeOriginalScalarEndPackageEdges
import all Linear.NativeOriginalScalarEndPackages
import all Linear.NativeOriginalScalarMapFormula
import all Linear.NativeOriginalScalarPackageActionRefold
import all Linear.NativeOriginalScalarPackages
import all Linear.NativeOriginalScalarRawIntrinsic
import all Linear.OriginalActualHBaseModuleObject
import all Linear.OriginalActualHBaseScalarRawMorphism
import all Linear.OriginalNativeScalarPackageAction
import all Linear.OriginalNativeScalarPackageActionRefold
import all Linear.OriginalRawScalarPackageRightInterface
import all Linear.OriginalSheafHRawMapPackage
import all Linear.SchemeModuleActualHBaseScalars
import all Linear.SchemeModuleActualHFunctorCalibration
import all Linear.SchemeModuleActualHGlobalSectionsModule
import all Linear.SchemeModuleActualHLinearCoefficientMap
import all Linear.SchemeModuleActualHScalarRingHom
import Lean.DeclarationRange
import Lean.Util.FoldConsts
set_option maxHeartbeats 5000
run_cmd do
  let env ← Lean.getEnv
  let selected : List String := ["Linear.AdditiveFunctorEndRingHom","Linear.AdditiveFunctorScalarSquare","Linear.NativeOriginalPublicScalarIntrinsic","Linear.NativeOriginalRawScalarIntrinsicPieces","Linear.NativeOriginalScalarEndPackageCalibration","Linear.NativeOriginalScalarEndPackageEdges","Linear.NativeOriginalScalarEndPackages","Linear.NativeOriginalScalarMapFormula","Linear.NativeOriginalScalarPackageActionRefold","Linear.NativeOriginalScalarPackages","Linear.NativeOriginalScalarRawIntrinsic","Linear.OriginalActualHBaseModuleObject","Linear.OriginalActualHBaseScalarRawMorphism","Linear.OriginalNativeScalarPackageAction","Linear.OriginalNativeScalarPackageActionRefold","Linear.OriginalRawScalarPackageRightInterface","Linear.OriginalSheafHRawMapPackage","Linear.SchemeModuleActualHBaseScalars","Linear.SchemeModuleActualHFunctorCalibration","Linear.SchemeModuleActualHGlobalSectionsModule","Linear.SchemeModuleActualHLinearCoefficientMap","Linear.SchemeModuleActualHScalarRingHom"]
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
