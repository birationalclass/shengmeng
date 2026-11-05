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
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
#check @LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom
#check @LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom
#check @LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
#print axioms LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
#check @LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic
#print axioms LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic
#check @LinearStudy.originalActualHBaseModuleObject_forget
#print axioms LinearStudy.originalActualHBaseModuleObject_forget
#check @LinearStudy.coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv
#print axioms LinearStudy.coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv
#check @LinearStudy.originalActualHSpecModuleObject
#print axioms LinearStudy.originalActualHSpecModuleObject
#check @LinearStudy.originalActualHSpecModuleObject_eq_restrictScalars
#print axioms LinearStudy.originalActualHSpecModuleObject_eq_restrictScalars
#check @LinearStudy.originalActualHSpecRestrictIso
#print axioms LinearStudy.originalActualHSpecRestrictIso
#check @LinearStudy.originalActualHSpecRestrictIso_forget_hom
#print axioms LinearStudy.originalActualHSpecRestrictIso_forget_hom
#check @LinearStudy.originalModuleScalarMorphism_eq_forget_smul_id
#print axioms LinearStudy.originalModuleScalarMorphism_eq_forget_smul_id
#check @LinearStudy.originalOrderedModuleHomologyScalarMorphism
#print axioms LinearStudy.originalOrderedModuleHomologyScalarMorphism
#check @LinearStudy.originalScalarSquareModuleIso
#print axioms LinearStudy.originalScalarSquareModuleIso
#check @LinearStudy.originalScalarSquareModuleIso_forget_hom
#print axioms LinearStudy.originalScalarSquareModuleIso_forget_hom
#check @LinearStudy.originalScalarSquareModuleIso_literal
#print axioms LinearStudy.originalScalarSquareModuleIso_literal
#check @LinearStudy.originalScalarSquareModuleIso_literal_forget_hom
#print axioms LinearStudy.originalScalarSquareModuleIso_literal_forget_hom
#check @LinearStudy.schemeModuleActualHObject_eq_ofCohomology
#print axioms LinearStudy.schemeModuleActualHObject_eq_ofCohomology
#print LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general
#print LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general
#print LinearStudy.originalActualHSpecModuleObject
#print LinearStudy.originalActualHSpecRestrictIso
#print LinearStudy.originalScalarSquareModuleIso
#print LinearStudy.originalScalarSquareModuleIso_literal
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general,false,false),(`LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHIntrinsicIso_general_forget_hom,true,true),(`LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general_forget_hom,true,true),(`LinearStudy.nativeIndependentFiniteNormalization_moduleCechActualHigherHSpecIso_general,false,false),(`LinearStudy.nativeGeneralModuleH_publicOperator_heq_intrinsic,true,true),(`LinearStudy.originalActualHBaseModuleObject_forget,true,true),(`LinearStudy.coordinateCanonicalCoefficientRingEquiv_toRingHom_eq_inv,true,true),(`LinearStudy.originalActualHSpecModuleObject,false,false),(`LinearStudy.originalActualHSpecModuleObject_eq_restrictScalars,true,true),(`LinearStudy.originalActualHSpecRestrictIso,false,false),(`LinearStudy.originalActualHSpecRestrictIso_forget_hom,true,true),(`LinearStudy.originalModuleScalarMorphism_eq_forget_smul_id,true,true),(`LinearStudy.originalOrderedModuleHomologyScalarMorphism,true,true),(`LinearStudy.originalScalarSquareModuleIso,false,false),(`LinearStudy.originalScalarSquareModuleIso_forget_hom,true,true),(`LinearStudy.originalScalarSquareModuleIso_literal,false,false),(`LinearStudy.originalScalarSquareModuleIso_literal_forget_hom,true,true),(`LinearStudy.schemeModuleActualHObject_eq_ofCohomology,true,true)]
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
