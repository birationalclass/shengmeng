module
import all Linear.DiscreteSchemeProjectorImageSupport
import all Linear.DiscreteSchemeProjectedExtInternalSupport
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleImage_open_isZero_of_map_zero
#print axioms LinearStudy.schemeModuleImage_open_isZero_of_map_zero
#check @LinearStudy.discreteSchemePushforwardOpenProjector_restrict_zero
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_restrict_zero
#check @LinearStudy.discreteSchemePushforwardOpenProjector_image_restrict_isZero
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_image_restrict_isZero
#check @LinearStudy.discreteSchemePushforwardOpenProjector_image_internalExt_restrict_isZero
#print axioms LinearStudy.discreteSchemePushforwardOpenProjector_image_internalExt_restrict_isZero
#check @LinearStudy.schemeModuleGlobalToInternalExtSections_precompose_restrict_zero
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections_precompose_restrict_zero
#check @LinearStudy.discreteSchemeProjectedExtClass_internal_section_restrict_zero
#print axioms LinearStudy.discreteSchemeProjectedExtClass_internal_section_restrict_zero
#check @LinearStudy.discreteSchemePointProjectedExtClass_internal_section_vanish_away
#print axioms LinearStudy.discreteSchemePointProjectedExtClass_internal_section_vanish_away
#print LinearStudy.schemeModuleGlobalToInternalExtSections
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections
#print LinearStudy.discreteSchemeProjectedExtClass
#print axioms LinearStudy.discreteSchemeProjectedExtClass
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleImage_open_isZero_of_map_zero,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_restrict_zero,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_image_restrict_isZero,true),(`LinearStudy.discreteSchemePushforwardOpenProjector_image_internalExt_restrict_isZero,true),(`LinearStudy.schemeModuleGlobalToInternalExtSections_precompose_restrict_zero,true),(`LinearStudy.discreteSchemeProjectedExtClass_internal_section_restrict_zero,true),(`LinearStudy.discreteSchemePointProjectedExtClass_internal_section_vanish_away,true)]
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
