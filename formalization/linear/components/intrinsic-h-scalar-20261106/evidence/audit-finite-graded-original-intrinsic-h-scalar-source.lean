module
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
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq
#print axioms LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq
#check @LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
#print axioms LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq
#check @LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
#print axioms LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic
#check @LinearStudy.nativeOriginalRawScalar_toPackage_heq
#print axioms LinearStudy.nativeOriginalRawScalar_toPackage_heq
#check @LinearStudy.nativeOriginalRawScalar_fromPackage_heq
#print axioms LinearStudy.nativeOriginalRawScalar_fromPackage_heq
#check @LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
#print axioms LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic
#check @LinearStudy.nativeOriginalScalarEndPackageLeft_heq
#print axioms LinearStudy.nativeOriginalScalarEndPackageLeft_heq
#check @LinearStudy.nativeOriginalScalarEndPackageRight_heq
#print axioms LinearStudy.nativeOriginalScalarEndPackageRight_heq
#check @LinearStudy.nativeOriginalRawScalarEndPackage
#print axioms LinearStudy.nativeOriginalRawScalarEndPackage
#check @LinearStudy.nativeOriginalMiddleScalarEndPackage
#print axioms LinearStudy.nativeOriginalMiddleScalarEndPackage
#check @LinearStudy.nativeOriginalIntrinsicScalarEndPackage
#print axioms LinearStudy.nativeOriginalIntrinsicScalarEndPackage
#check @LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
#print axioms LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap
#check @LinearStudy.nativeOriginalScalarPackageAction_refold_heq
#print axioms LinearStudy.nativeOriginalScalarPackageAction_refold_heq
#check @LinearStudy.nativeOriginalScalarPackageLeft_eq
#print axioms LinearStudy.nativeOriginalScalarPackageLeft_eq
#check @LinearStudy.nativeOriginalScalarPackageMaps_heq
#print axioms LinearStudy.nativeOriginalScalarPackageMaps_heq
#check @LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
#print axioms LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq
#check @LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic
#print axioms LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic
#check @LinearStudy.originalActualHBaseModuleObject
#print axioms LinearStudy.originalActualHBaseModuleObject
#check @LinearStudy.originalActualHBaseScalarRawMorphism
#print axioms LinearStudy.originalActualHBaseScalarRawMorphism
#check @LinearStudy.originalNativeScalarPackageAction_heq
#print axioms LinearStudy.originalNativeScalarPackageAction_heq
#check @LinearStudy.originalNativeScalarPackageAction_refold_heq
#print axioms LinearStudy.originalNativeScalarPackageAction_refold_heq
#check @LinearStudy.originalRawScalarNativePackage_projection
#print axioms LinearStudy.originalRawScalarNativePackage_projection
#check @LinearStudy.originalRawScalarNativePackage_carrier_fold
#print axioms LinearStudy.originalRawScalarNativePackage_carrier_fold
#check @LinearStudy.originalSheafHRawMapPackage
#print axioms LinearStudy.originalSheafHRawMapPackage
#check @LinearStudy.originalSheafHRawMapPackage_snd_heq
#print axioms LinearStudy.originalSheafHRawMapPackage_snd_heq
#print LinearStudy.nativeOriginalRawScalarEndPackage
#print LinearStudy.nativeOriginalMiddleScalarEndPackage
#print LinearStudy.nativeOriginalIntrinsicScalarEndPackage
#print LinearStudy.originalActualHBaseModuleObject
#print LinearStudy.originalSheafHRawMapPackage
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.nativeOriginalRawScalarOnPublicGroup_heq,true,true),(`LinearStudy.nativeOriginalPublicScalarToIntrinsicPackage_heq,true,true),(`LinearStudy.nativeOriginalActualHPublicScalarOperator_heq_intrinsic,true,true),(`LinearStudy.nativeOriginalRawScalar_toPackage_heq,true,true),(`LinearStudy.nativeOriginalRawScalar_fromPackage_heq,true,true),(`LinearStudy.nativeOriginalScalarEndPackages_heq_intrinsic,true,true),(`LinearStudy.nativeOriginalScalarEndPackageLeft_heq,true,true),(`LinearStudy.nativeOriginalScalarEndPackageRight_heq,true,true),(`LinearStudy.nativeOriginalRawScalarEndPackage,false,false),(`LinearStudy.nativeOriginalMiddleScalarEndPackage,false,false),(`LinearStudy.nativeOriginalIntrinsicScalarEndPackage,false,false),(`LinearStudy.nativeOriginalActualHScalarOperator_eq_rawMap,true,true),(`LinearStudy.nativeOriginalScalarPackageAction_refold_heq,true,true),(`LinearStudy.nativeOriginalScalarPackageLeft_eq,true,true),(`LinearStudy.nativeOriginalScalarPackageMaps_heq,true,true),(`LinearStudy.nativeOriginalScalarRawToIntrinsicPackage_heq,true,true),(`LinearStudy.nativeOriginalActualHScalarOperator_heq_intrinsic,true,true),(`LinearStudy.originalActualHBaseModuleObject,false,false),(`LinearStudy.originalActualHBaseScalarRawMorphism,true,true),(`LinearStudy.originalNativeScalarPackageAction_heq,true,true),(`LinearStudy.originalNativeScalarPackageAction_refold_heq,true,true),(`LinearStudy.originalRawScalarNativePackage_projection,true,true),(`LinearStudy.originalRawScalarNativePackage_carrier_fold,true,true),(`LinearStudy.originalSheafHRawMapPackage,false,false),(`LinearStudy.originalSheafHRawMapPackage_snd_heq,true,true)]
  let env ← Lean.getEnv
  for (n,want,wantTheorem) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if wantTheorem then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
