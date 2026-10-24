module
import all Linear.SchemeModuleExtSectionTraceSourceNaturality
import all Linear.DiscreteSchemeOpenIdempotent
import all Linear.DiscreteSchemePushforwardOpenProjector
import all Linear.DiscreteSchemeProjectedExtTrace
import all Linear.DiscreteSchemePointIdempotents
import all Linear.DiscreteSchemePointProjectedExtDecomposition
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleUnitHomGlobalSections_symm_map
#print axioms LinearStudy.schemeModuleUnitHomGlobalSections_symm_map
#check @LinearStudy.schemeModuleExtSectionTracePairing_source_naturality
#print axioms LinearStudy.schemeModuleExtSectionTracePairing_source_naturality
#check @LinearStudy.schemeModuleExtSectionTracePairing_zero_of_source_projector
#print axioms LinearStudy.schemeModuleExtSectionTracePairing_zero_of_source_projector
#check @LinearStudy.discreteScheme_exists_open_idempotent
#print axioms LinearStudy.discreteScheme_exists_open_idempotent
#check @LinearStudy.discreteSchemeOpenIdempotent
#print axioms LinearStudy.discreteSchemeOpenIdempotent
#check @LinearStudy.discreteSchemeOpenIdempotent_restrict_one
#print axioms LinearStudy.discreteSchemeOpenIdempotent_restrict_one
#check @LinearStudy.discreteSchemeOpenIdempotent_restrict_complement_zero
#print axioms LinearStudy.discreteSchemeOpenIdempotent_restrict_complement_zero
#check @LinearStudy.discreteSchemeOpenIdempotent_idempotent
#print axioms LinearStudy.discreteSchemeOpenIdempotent_idempotent
#check @LinearStudy.discreteSchemeOpenIdempotent_restrict_one_of_le
#print axioms LinearStudy.discreteSchemeOpenIdempotent_restrict_one_of_le
#check @LinearStudy.discreteSchemeOpenIdempotent_restrict_zero_of_le_complement
#print axioms LinearStudy.discreteSchemeOpenIdempotent_restrict_zero_of_le_complement
#check @LinearStudy.discreteSchemePushforwardOpenProjector
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector
#check @LinearStudy.discreteSchemePushforwardOpenProjector_idempotent
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_idempotent
#check @LinearStudy.discreteSchemePushforwardOpenProjector_app
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_app
#check @LinearStudy.discreteSchemePushforwardOpenProjector_app_one
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_app_one
#check @LinearStudy.discreteSchemePushforwardOpenProjector_app_zero
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_app_zero
#check @LinearStudy.discreteSchemeProjectedExtClass
#print axioms LinearStudy.discreteSchemeProjectedExtClass
#check @LinearStudy.discreteSchemeProjectedExtClass_fixed
#print axioms LinearStudy.discreteSchemeProjectedExtClass_fixed
#check @LinearStudy.discreteSchemeProjectedExtClass_trace
#print axioms LinearStudy.discreteSchemeProjectedExtClass_trace
#check @LinearStudy.discreteSchemeProjectedExtClass_trace_complement_zero
#print axioms LinearStudy.discreteSchemeProjectedExtClass_trace_complement_zero
#check @LinearStudy.discreteSchemeProjectedExtClass_internal_section
#print axioms LinearStudy.discreteSchemeProjectedExtClass_internal_section
#check @LinearStudy.discreteSchemePointOpen
#print axioms LinearStudy.discreteSchemePointOpen
#check @LinearStudy.discreteSchemePointIdempotent
#print axioms LinearStudy.discreteSchemePointIdempotent
#check @LinearStudy.discreteSchemePointIdempotent_selector
#print axioms LinearStudy.discreteSchemePointIdempotent_selector
#check @LinearStudy.discreteSchemePointIdempotent_sum
#print axioms LinearStudy.discreteSchemePointIdempotent_sum
#check @LinearStudy.discreteSchemePointIdempotent_mul_eq_zero
#print axioms LinearStudy.discreteSchemePointIdempotent_mul_eq_zero
#check @LinearStudy.instDecidableEqCarrierCarrierCommRingCat_linear
#print axioms LinearStudy.instDecidableEqCarrierCarrierCommRingCat_linear
#check @LinearStudy.discreteSchemePushforwardPointProjector
#print axioms LinearStudy.discreteSchemePushforwardPointProjector
#check @LinearStudy.discreteSchemePushforwardPointProjector_sum
#print axioms LinearStudy.discreteSchemePushforwardPointProjector_sum
#check @LinearStudy.discreteSchemePushforwardPointProjector_comp_eq_zero
#print axioms LinearStudy.discreteSchemePushforwardPointProjector_comp_eq_zero
#check @LinearStudy.discreteSchemePointProjectedExtClass
#print axioms LinearStudy.discreteSchemePointProjectedExtClass
#check @LinearStudy.discreteSchemePointProjectedExtClass_sum
#print axioms LinearStudy.discreteSchemePointProjectedExtClass_sum
#check @LinearStudy.discreteSchemePointProjectedExtClass_trace_sum
#print axioms LinearStudy.discreteSchemePointProjectedExtClass_trace_sum
#check @LinearStudy.artinianSchemePointProjectedExtClass_sum
#print axioms LinearStudy.artinianSchemePointProjectedExtClass_sum
#print LinearStudy.discreteSchemeOpenIdempotent
#print LinearStudy.discreteSchemePushforwardOpenProjector
#print LinearStudy.discreteSchemeProjectedExtClass
#print LinearStudy.discreteSchemePointOpen
#print LinearStudy.discreteSchemePointIdempotent
#print LinearStudy.instDecidableEqCarrierCarrierCommRingCat_linear
#print LinearStudy.discreteSchemePushforwardPointProjector
#print LinearStudy.discreteSchemePointProjectedExtClass
#print LinearStudy.schemeModuleExtSectionTracePairing
#print axioms LinearStudy.schemeModuleExtSectionTracePairing
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleUnitHomGlobalSections_symm_map,true),(`LinearStudy.schemeModuleExtSectionTracePairing_source_naturality,true),(`LinearStudy.schemeModuleExtSectionTracePairing_zero_of_source_projector,true),(`LinearStudy.discreteScheme_exists_open_idempotent,true),(`LinearStudy.discreteSchemeOpenIdempotent,false),(`LinearStudy.discreteSchemeOpenIdempotent_restrict_one,true),(`LinearStudy.discreteSchemeOpenIdempotent_restrict_complement_zero,true),(`LinearStudy.discreteSchemeOpenIdempotent_idempotent,true),(`LinearStudy.discreteSchemeOpenIdempotent_restrict_one_of_le,true),(`LinearStudy.discreteSchemeOpenIdempotent_restrict_zero_of_le_complement,true),(`LinearStudy.discreteSchemePushforwardOpenProjector,false),(`LinearStudy.discreteSchemePushforwardOpenProjector_idempotent,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_app,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_app_one,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_app_zero,true),(`LinearStudy.discreteSchemeProjectedExtClass,false),(`LinearStudy.discreteSchemeProjectedExtClass_fixed,true),(`LinearStudy.discreteSchemeProjectedExtClass_trace,true),(`LinearStudy.discreteSchemeProjectedExtClass_trace_complement_zero,true),(`LinearStudy.discreteSchemeProjectedExtClass_internal_section,true),(`LinearStudy.discreteSchemePointOpen,false),(`LinearStudy.discreteSchemePointIdempotent,false),(`LinearStudy.discreteSchemePointIdempotent_selector,true),(`LinearStudy.discreteSchemePointIdempotent_sum,true),(`LinearStudy.discreteSchemePointIdempotent_mul_eq_zero,true),(`LinearStudy.instDecidableEqCarrierCarrierCommRingCat_linear,false),(`LinearStudy.discreteSchemePushforwardPointProjector,false),(`LinearStudy.discreteSchemePushforwardPointProjector_sum,true),(`LinearStudy.discreteSchemePushforwardPointProjector_comp_eq_zero,true),(`LinearStudy.discreteSchemePointProjectedExtClass,false),(`LinearStudy.discreteSchemePointProjectedExtClass_sum,true),(`LinearStudy.discreteSchemePointProjectedExtClass_trace_sum,true),(`LinearStudy.artinianSchemePointProjectedExtClass_sum,true)]
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
