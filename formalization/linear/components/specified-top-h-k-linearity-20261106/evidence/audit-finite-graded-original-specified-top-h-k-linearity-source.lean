module
import all Linear.NativeGeneralSpecifiedTopHIntrinsicSpecIso
import all Linear.NativeGeneralSpecifiedTopHIntrinsicForgetIso
import all Linear.OriginalInverseCompositeForgetIso
set_option maxHeartbeats 5000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget
#check @LinearStudy.originalInverseCompositeForgetIso
#print axioms LinearStudy.originalInverseCompositeForgetIso
#print LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool × Bool) := [(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general,false,false),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualKLinearIso_general_forget,true,true),(`LinearStudy.originalInverseCompositeForgetIso,true,true)]
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
