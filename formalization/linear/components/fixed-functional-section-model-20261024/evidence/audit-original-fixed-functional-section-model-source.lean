module
import all Linear.NativeHomogeneousShiftSectionMap
import all Linear.NativeHomogeneousEmbeddingSectionFormula
import all Linear.OriginalPolynomialSectionImageEquality
import all Linear.OriginalPolynomialInjectiveImageLift
import all Linear.OriginalGradedPolynomialSectionImage
import all Linear.OriginalNormalizationHomogeneousEmbeddingWitness
import all Linear.OriginalNormalizationPolynomialSectionEmbedding
import all Linear.OriginalPolynomialSectionClassEquality
import all Linear.OriginalPolynomialSectionImageProjections
import all Linear.OriginalNormalizationFixedFunctionalSectionModel
import all Linear.OriginalRetainedPolynomialSectionImage
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeProjectiveModuleSheafMap_homogeneousGlobalSection
#print axioms LinearStudy.nativeProjectiveModuleSheafMap_homogeneousGlobalSection
#check @LinearStudy.nativeHomogeneousGlobalSection_indexTransport
#print axioms LinearStudy.nativeHomogeneousGlobalSection_indexTransport
#check @LinearStudy.nativeProjectiveHomogeneousInjection_exists_zero_degree_mono_sectionFormula
#print axioms LinearStudy.nativeProjectiveHomogeneousInjection_exists_zero_degree_mono_sectionFormula
#check @LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_image
#print axioms LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_image
#check @LinearStudy.originalPolynomial_exists_of_injective_image
#print axioms LinearStudy.originalPolynomial_exists_of_injective_image
#check @LinearStudy.originalGradedPolynomialSectionImageStatement
#print axioms LinearStudy.originalGradedPolynomialSectionImageStatement
#check @LinearStudy.originalGradedPolynomialSectionImageStatement_of_formula
#print axioms LinearStudy.originalGradedPolynomialSectionImageStatement_of_formula
#check @LinearStudy.originalNormalizationDual_exists_homogeneous_embedding_witness_above
#print axioms LinearStudy.originalNormalizationDual_exists_homogeneous_embedding_witness_above
#check @LinearStudy.originalNormalizationDual_exists_polynomial_section_embedding_above
#print axioms LinearStudy.originalNormalizationDual_exists_polynomial_section_embedding_above
#check @LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_eq
#print axioms LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_eq
#check @LinearStudy.originalGradedPolynomialSectionImageStatement_polynomial_images
#print axioms LinearStudy.originalGradedPolynomialSectionImageStatement_polynomial_images
#check @LinearStudy.originalNormalizationFixedFunctionalSectionModelStatement
#print axioms LinearStudy.originalNormalizationFixedFunctionalSectionModelStatement
#check @LinearStudy.originalNormalization_exists_fixed_functional_and_section_model_above
#print axioms LinearStudy.originalNormalization_exists_fixed_functional_and_section_model_above
#check @LinearStudy.originalGradedPolynomialSectionImageStatement_any_polynomial
#print axioms LinearStudy.originalGradedPolynomialSectionImageStatement_any_polynomial
#print LinearStudy.originalGradedPolynomialSectionImageStatement
#print LinearStudy.originalNormalizationFixedFunctionalSectionModelStatement
#print LinearStudy.nativeCoextensionFixedPolynomialFunctionalStatement
#print axioms LinearStudy.nativeCoextensionFixedPolynomialFunctionalStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeProjectiveModuleSheafMap_homogeneousGlobalSection,true),(`LinearStudy.nativeHomogeneousGlobalSection_indexTransport,true),(`LinearStudy.nativeProjectiveHomogeneousInjection_exists_zero_degree_mono_sectionFormula,true),(`LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_image,true),(`LinearStudy.originalPolynomial_exists_of_injective_image,true),(`LinearStudy.originalGradedPolynomialSectionImageStatement,false),(`LinearStudy.originalGradedPolynomialSectionImageStatement_of_formula,true),(`LinearStudy.originalNormalizationDual_exists_homogeneous_embedding_witness_above,true),(`LinearStudy.originalNormalizationDual_exists_polynomial_section_embedding_above,true),(`LinearStudy.originalProjectivePolynomialSection_eq_of_quotient_eq,true),(`LinearStudy.originalGradedPolynomialSectionImageStatement_polynomial_images,true),(`LinearStudy.originalNormalizationFixedFunctionalSectionModelStatement,false),(`LinearStudy.originalNormalization_exists_fixed_functional_and_section_model_above,true),(`LinearStudy.originalGradedPolynomialSectionImageStatement_any_polynomial,true)]
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
