module
import all Linear.SurjectiveBaseCoefficientQuotient
import all Linear.CoextensionOriginalCoefficientQuotient
import all Linear.OriginalCutEquationCoefficientQuotientDual
import all Linear.FieldDualNativeCoextensionSource
import all Linear.OriginalCutEquationCoefficientNativeDual
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.surjectiveBaseCoefficientQuotientEquiv
#print axioms LinearStudy.surjectiveBaseCoefficientQuotientEquiv
#check @LinearStudy.surjectiveBaseCoefficientQuotientEquiv_mk
#print axioms LinearStudy.surjectiveBaseCoefficientQuotientEquiv_mk
#check @LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv
#print axioms LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv
#check @LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv_mk
#print axioms LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv_mk
#check @LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv
#print axioms LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv
#check @LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv_mk
#print axioms LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv_mk
#check @LinearStudy.projectivePulledCutEquationCoefficientQuotientDualStatement
#print axioms LinearStudy.projectivePulledCutEquationCoefficientQuotientDualStatement
#check @LinearStudy.projectivePulledCutEquation_coefficient_quotient_dual_of_fiber_dual
#print axioms LinearStudy.projectivePulledCutEquation_coefficient_quotient_dual_of_fiber_dual
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_quotient_dual_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_quotient_dual_open
#check @LinearStudy.fieldDualNativeCoextensionSourceEquiv
#print axioms LinearStudy.fieldDualNativeCoextensionSourceEquiv
#check @LinearStudy.fieldDualNativeCoextensionSourceEquiv_apply
#print axioms LinearStudy.fieldDualNativeCoextensionSourceEquiv_apply
#check @LinearStudy.projectivePulledCutOriginalRingMap
#print axioms LinearStudy.projectivePulledCutOriginalRingMap
#check @LinearStudy.projectivePulledCutOriginalRingMap_mk
#print axioms LinearStudy.projectivePulledCutOriginalRingMap_mk
#check @LinearStudy.projectivePulledCutOriginalRingMap_surjective
#print axioms LinearStudy.projectivePulledCutOriginalRingMap_surjective
#check @LinearStudy.projectivePulledCutEquationCoefficientNativeDualStatement
#print axioms LinearStudy.projectivePulledCutEquationCoefficientNativeDualStatement
#check @LinearStudy.projectivePulledCutEquation_native_dual_of_quotient_dual
#print axioms LinearStudy.projectivePulledCutEquation_native_dual_of_quotient_dual
#check @LinearStudy.projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open
#print axioms LinearStudy.projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open
#print LinearStudy.surjectiveBaseCoefficientQuotientEquiv
#print LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv
#print LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv
#print LinearStudy.projectivePulledCutEquationCoefficientQuotientDualStatement
#print LinearStudy.fieldDualNativeCoextensionSourceEquiv
#print LinearStudy.projectivePulledCutOriginalRingMap
#print LinearStudy.projectivePulledCutEquationCoefficientNativeDualStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.surjectiveBaseCoefficientQuotientEquiv,false),(`LinearStudy.surjectiveBaseCoefficientQuotientEquiv_mk,true),(`LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv,false),(`LinearStudy.surjectiveBaseCoefficientQuotientOriginalFieldEquiv_mk,true),(`LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv,false),(`LinearStudy.coextensionOriginalCoefficientQuotientFiberEquiv_mk,true),(`LinearStudy.projectivePulledCutEquationCoefficientQuotientDualStatement,false),(`LinearStudy.projectivePulledCutEquation_coefficient_quotient_dual_of_fiber_dual,true),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_coefficient_quotient_dual_open,true),(`LinearStudy.fieldDualNativeCoextensionSourceEquiv,false),(`LinearStudy.fieldDualNativeCoextensionSourceEquiv_apply,true),(`LinearStudy.projectivePulledCutOriginalRingMap,false),(`LinearStudy.projectivePulledCutOriginalRingMap_mk,true),(`LinearStudy.projectivePulledCutOriginalRingMap_surjective,true),(`LinearStudy.projectivePulledCutEquationCoefficientNativeDualStatement,false),(`LinearStudy.projectivePulledCutEquation_native_dual_of_quotient_dual,true),(`LinearStudy.projectivePulledCutEquation_originalSetup_exists_native_coefficient_dual_open,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if want then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
