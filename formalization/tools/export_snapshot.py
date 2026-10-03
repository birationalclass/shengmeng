"""Publish only project sources and verified evidence, never .lake or local user data."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, zipfile

project, destination = map(Path, sys.argv[1:3])
names = {
    'ImportedProjectiveCechVanishing.lean': ['imported_projective_laurent_cech_positive_twist_vanishing'],
    'ImportedProjectiveCechFiniteness.lean': ['imported_projective_laurent_cech_cohomology_finite'],
    'ActualRelativeCechCycleModule.lean': ['actual_relative_cech_cycles_rees_module'],
    'ActualRelativeCechGradedAction.lean': ['actual_relative_ideal_section_mul_mem', 'actual_relative_cech_graded_action_on_classes'],
    'ActualRelativeCechMultiplication.lean': ['actual_base_ideal_local_pullback_mem', 'actual_relative_cech_graded_cocycle_multiplication'],
    'ActualProperCechCover.lean': ['exists_actual_proper_affine_cech_cover'],
    'ActualCechModule.lean': ['actual_closed_cech_module_action'],
    'ActualCechScalars.lean': ['actual_cech_difference_scale', 'actual_cech_boundary_scale', 'actual_cech_pullback_scale_zero', 'actual_cech_pullback_scale_one', 'actual_closed_cech_scalar_on_cocycles'],
    'RelativeCechFormalComparison.lean': ['actual_relative_power_inclusion_comp', 'actual_relative_formal_functions_bijective_of_cech_kernel_vanishing'],
    'RelativeCechSectionLifting.lean': ['actual_relative_section_lifting_of_cech_kernel_vanishing'],
    'ActualCechKernelLifting.lean': ['actual_closed_cech_lifting_of_cohomology_kernel_bound'],
    'ActualCechCohomologyExact.lean': ['actual_closed_cech_cohomology_exact'],
    'ActualCechClosedTransition.lean': ['actual_closed_cech_connecting_naturality'],
    'ActualCechClosedObstruction.lean': ['actual_closed_cech_obstruction_independent_of_lifts', 'actual_closed_cech_obstruction_zero_iff', 'actual_closed_cech_connecting_exact'],
    'ActualCechClosedLifting.lean': ['actual_section_restriction_naturality', 'actual_cech_pullback_difference', 'actual_closed_cech_local_lift_pullback', 'actual_closed_cech_section_lifting_criterion'],
    'ActualCechSections.lean': ['actual_section_restriction_trans', 'actual_cech_boundary_difference_zero', 'actual_cech_global_sections_exact'],
    'RelativeFormalInjectivity.lean': ['actual_relative_formal_functions_injective'],
    'AdicComparisonInjectivity.lean': ['adic_comparison_injective_of_uniform_kernel_bound'],
    'RelativeKernelBound.lean': ['actual_relative_kernel_uniform_bound'],
    'RelativeKernelFiniteness.lean': ['actual_relative_kernel_rees_module_finite'],
    'RelativeKernelIntegral.lean': ['integral_of_all_valuation_subrings', 'actual_relative_kernel_monomial_integral'],
    'ReesFractionField.lean': ['polynomial_scaled_mem_rees', 'rees_algebra_polynomial_fraction_field'],
    'RelativeKernelWeighted.lean': ['actual_relative_kernel_weighted_valuation_mem'],
    'AffineValuationBase.lean': ['actual_affine_ring_base_sections', 'actual_affine_ring_base_dominant', 'actual_affine_valuation_generic_dominant'],
    'WeightedIdealExtension.lean': ['weighted_subring_ideal_mul', 'weighted_ideal_extension_mem'],
    'RelativeKernelValuative.lean': ['actual_proper_birational_valuation_lift', 'actual_relative_kernel_valuative_contraction'],
    'ProperBirationalGlobalFiniteness.lean': ['actual_proper_birational_global_functions_finite'],
    'RelativeKernelFiltration.lean': ['actual_relative_kernel_ideal_mono', 'actual_relative_kernel_ideal_mul', 'actual_relative_kernel_filtration'],
    'PullbackIdealProducts.lean': ['actual_affine_ideal_pullback_mul', 'actual_open_ideal_pullback_mul', 'actual_ideal_pullback_mul_over_affine_base', 'actual_ideal_pullback_pow_over_affine_base'],
    'AffinePullbackIdeal.lean': ['actual_affine_ideal_pushforward', 'actual_affine_ideal_pullback'],
    'RelativeFormalApproximation.lean': ['actual_relative_quotient_map_constant', 'actual_relative_restriction_transition', 'actual_relative_quotient_map_transition', 'actual_relative_formal_functions_bijective_of_uniform_approximation'],
    'AdicApproximationComparison.lean': ['adic_comparison_bijective_of_uniform_approximation'],
    'ActualProperNegativityFull.lean': ['actual_proper_negativity_of_actual_formal_functions'],
    'GlobalClosedFiberConnectedness.lean': ['actual_closed_fibers_connected_of_affine_formal_functions'],
    'AffineNeighborhoodFiber.lean': ['actual_restricted_fiber_connected_iff'],
    'ActualProperSupportDichotomy.lean': ['actual_proper_support_dichotomy_of_connected_closed_fibers'],
    'ClosedFiberCompleteness.lean': ['actual_closed_fiber_proper_over_ground_field'],
    'ClosedFiberSupportDetection.lean': ['actual_fiber_closed_subset_dichotomy_of_closed_points'],
    'ConstructibleClosedPoint.lean': ['noetherian_constructible_contains_closed_point'],
    'RelativeFormalConnectedness.lean': ['actual_closed_fiber_connected_of_relative_formal_functions'],
    'ClosedFiberInfinitesimalIdempotent.lean': ['actual_closed_fiber_infinitesimal_nontrivial_idempotent'],
    'ClosedPointFiberThickenings.lean': ['actual_closed_point_ideal_support', 'actual_closed_point_ideal_top', 'actual_closed_point_ideal_top_maximal', 'actual_closed_point_completion_local'],
    'RelativeInfinitesimalIdempotents.lean': ['actual_relative_power_inclusion_point', 'actual_compatible_clopen_nontrivial_idempotent', 'actual_relative_infinitesimal_nontrivial_idempotent'],
    'RelativeFormalFunctionsMap.lean': ['actual_relative_power_projection_square', 'actual_relative_formal_functions_evaluation'],
    'ActualProperNegativityIff.lean': ['actual_proper_negativity_effectivity_iff'],
    'ActualProperNegativity.lean': ['actual_proper_negativity_part_one'],
    'ActualProperAffineNegativity.lean': ['actual_proper_affine_negativity_part_one'],
    'HartshorneCartierModification.lean': ['exists_actual_hartshorne_cartier_modification'],
    'BirationalCycleComposition.lean': ['actual_cycle_push_at_codimension_one_preimage', 'actual_proper_birational_weil_pushforward_comp'],
    'CanonicalCartierPushPull.lean': ['actual_canonical_real_cartier_push_pull'],
    'ProjectiveProductCartierSections.lean': ['exists_actual_projective_product_cartier_sections'],
    'NormalHartshorneModification.lean': ['exists_actual_normal_hartshorne_modification'],
    'BirationalComposition.lean': ['birational_of_actual_generic_stalk_isIso', 'actual_birational_morphism_comp'],
    'HartshorneFiniteModification.lean': ['exists_actual_hartshorne_finite_modification'],
    'FiniteProperRelativeProduct.lean': ['exists_actual_finite_proper_relative_product'],
    'AffineProductCharts.lean': ['actual_affine_product_chart'],
    'HartshorneProjectionFinite.lean': ['actual_graph_projection_isImmersion', 'hartshorne_graph_second_projection_finite'],
    'HartshorneAffineCover.lean': ['exists_actual_hartshorne_affine_projective_cover'],
    'StandardProjectiveProper.lean': ['projective_degree_zero_inclusion_bijective', 'actual_standard_projective_space_proper'],
    'FiniteTypeProjectiveImmersion.lean': ['actual_projective_affine_chart_inclusion_over', 'exists_actual_affine_finite_type_projective_immersion'],
    'ProjectiveAffineChartAlgebra.lean': ['actual_projective_chart_evaluation_constant', 'actual_projective_chart_evaluation_coordinate', 'exists_actual_projective_affine_chart_quotient'],
    'AffineFormalFunctions.lean': ['completion_power_quotient_eval', 'completion_power_quotient_transition', 'adic_completion_power_eval_transition', 'actual_affine_formal_functions_bijective'],
    'AffineThickeningSections.lean': ['actual_affine_thickening_sections_pullback', 'actual_affine_thickening_sections_transition'],
    'InfinitesimalIdempotents.lean': ['actual_power_thickening_inclusion_point', 'actual_infinitesimal_nontrivial_idempotent'],
    'ClopenCharacteristicSection.lean': ['actual_clopen_characteristic_exists_unique', 'actual_clopen_characteristic_germ', 'actual_clopen_characteristic_idempotent', 'actual_clopen_characteristic_pullback'],
    'SchemeClopenIdempotent.lean': ['actual_clopen_nontrivial_global_idempotent', 'actual_scheme_connected_of_global_idempotents_trivial'],
    'ProperBirationalSections.lean': ['proper_normal_birational_open_functions_isIso', 'proper_normal_birational_open_functions_bijective'],
    'ProperBirationalStructureSheaf.lean': ['proper_normal_birational_structure_sheaf_isIso'],
    'ProperBirationalFunctions.lean': ['birational_functionField_pullback_bijective', 'proper_normal_birational_affine_functions_bijective'],
    'ActualProjectiveNegativityIff.lean': ['actual_projective_negativity_effectivity_iff'],
    'ActualProjectiveNegativity.lean': ['actual_projective_negativity_part_one'],
    'RelativeProjectiveEmbedding.lean': ['actual_relative_projective_embedding_cartier_sections'],
    'ActualOpenNef.lean': ['actual_relative_nef_on_target_open'],
    'ActualOpenPushforward.lean': ['actual_weil_cycle_pushforward_isWeil', 'actual_real_cartier_pushforward_effective_on_open'],
    'CartierOpenRestriction.lean': ['actual_cartier_open_restriction_coefficient', 'actual_real_cartier_open_restriction_cycle'],
    'ActualProjectiveAffineNegativity.lean': ['actual_projective_affine_negativity'],
    'ProjectiveExceptionalWitness.lean': ['exists_actual_projective_exceptional_cartier'],
    'ProjPolynomialSections.lean': ['mvPolynomial_degree_zero_adjoin_variables', 'exists_actual_projective_space_cartier_sections'],
    'ProjStandardSections.lean': ['exists_actual_proj_sections_of_generators'],
    'ProjCartierSections.lean': ['exists_actual_proj_cartier_affine_section_cover'],
    'ProjCartierAtlas.lean': ['proj_coordinate_generic_of_point', 'exists_actual_proj_cartier_atlas'],
    'ProjCoordinatePullback.lean': ['pulled_proj_coordinate_ratio_local', 'pulled_proj_coordinate_ratio_ne_zero', 'pulled_proj_coordinate_ratio_mul'],
    'ProjCoordinateRatios.lean': ['proj_coordinate_ratio_stalk_unit_iff', 'proj_coordinate_ratio_stalk_mul', 'proj_coordinate_ratio_section_germ'],
    'ActualNegativityAffineSections.lean': ['actual_negativity_of_affine_section_cover'],
    'CartierInverse.lean': ['cartierAtlas_inverse_coefficient', 'complete_integral_curve_cartier_intersection_inverse'],
    'CartierAffineSections.lean': ['complete_integral_curve_positive_of_affine_section_cover'],
    'NormalizedCartierSigns.lean': ['complete_integral_curve_effective_cartier_intersection_signs'],
    'CompleteCurveAffineAvoidance.lean': ['complete_integral_curve_not_affine', 'complete_integral_curve_meets_complement_affine_open'],
    'ActualNegativityConstruction.lean': ['actual_negativity_of_strictly_negative_cartier'],
    'EffectiveExceptionalWitness.lean': ['exists_effective_exceptional_covering_cartier_twist'],
    'NormalizedPrincipalInvariance.lean': ['complete_integral_curve_ambient_cartier_principal_invariance'],
    'CartierEffectiveTwist.lean': ['exists_effective_cartier_rational_twist'],
    'ActualConnectedSupport.lean': ['actual_connected_contracted_scheme_support_dichotomy'],
    'ConnectedCurveCrossing.lean': ['connected_closed_subset_crossing_component', 'connected_complete_scheme_actual_crossing_curve'],
    'CompleteCurveAvoiding.lean': ['exists_complete_integral_curve_through_closed_point_avoiding'],
    'AffineCurveAvoiding.lean': ['affine_integral_curve_through_maximal_avoiding'],
    'AffineLineAvoiding.lean': ['affine_line_through_point_avoiding_polynomial'],
    'ActualNegativityWitness.lean': ['actualRealCartierCoefficients_apply', 'actual_negativity_of_antiample_witness'],
    'NegativeActualCenter.lean': ['actual_cycle_coefficient_over_isomorphism_open', 'actual_negative_coefficient_image_in_center'],
    'ZeroPrimeCurve.lean': ['zero_weil_coefficient_outside_geometric_support', 'zero_exceptional_prime_actual_curve_nonnegative_intersection'],
    'ExceptionalCompleteCurve.lean': ['exceptional_closed_point_complete_contracted_curve'],
    'NonisolatedCompleteCurve.lean': ['nonisolated_point_positive_irreducible_component', 'exists_complete_integral_curve_through_nonisolated_closed_point'],
    'IntegralClosedSubscheme.lean': ['vanishingIdeal_subscheme_isReduced', 'closed_irreducible_actual_subscheme_properties'],
    'CompleteCurveThroughPoint.lean': ['affine_chart_not_field_at_nonGeneric_point', 'dimension_one_of_curve_domain', 'exists_complete_integral_curve_through_closed_point'],
    'CompleteCurveClosure.lean': ['dominant_functionField_constants_comp', 'quasiCompact_integral_actual_image_isIntegral', 'complete_integral_curve_actual_closure'],
    'FunctionFieldDimension.lean': ['finiteType_domain_dimension_of_trdeg_le_one', 'affine_chart_dimension_of_functionField_trdeg_le_one', 'integral_scheme_dimension_of_functionField_trdeg_le_one'],
    'AffineCurveThroughPoint.lean': ['integral_extension_krullDimLE_one', 'affine_integral_curve_through_maximal'],
    'AffineLineThroughPoint.lean': ['affine_line_kernel_below_point'],
    'ActualCycleProjectionCases.lean': ['actual_point_image_curve_cycle_zero', 'actual_complete_curve_cycle_projection_cases'],
    'ActualRelativeNef.lean': ['actual_relative_nef_negative_iff', 'actual_relative_nef_canonical_pullback'],
    'CanonicalRealPullbackIntersection.lean': ['actualCartierPullback_data', 'complete_integral_curve_canonical_real_pullback_intersection'],
    'FixedCartierPullbackIntersection.lean': ['complete_curve_cartier_intersection_of_actual_pullback'],
    'EmbeddedCurveProjection.lean': ['residueDegree_precomp_closedImmersion', 'embedded_curve_actual_cycle_push', 'exists_embedded_complete_curve_real_projection_formula'],
    'ActualProjectionFormula.lean': ['exists_complete_integral_curve_actual_real_projection_formula'],
    'AmbientCurveProjection.lean': ['complete_integral_curve_ambient_real_projection'],
    'ImageCycleMultiplicity.lean': ['closedImmersion_residueFieldMap_bijective', 'residueDegree_comp_closedImmersion', 'actual_image_residueDegree_functionField'],
    'CurveImageCases.lean': ['closedImmersion_height_eq', 'integral_scheme_point_or_curve', 'complete_integral_curve_actual_image_dichotomy'],
    'CurveImageGeometry.lean': ['actual_image_isReduced', 'proper_integral_actual_image_isIntegral', 'complete_integral_curve_actual_image_properties'],
    'CurveCycleProjection.lean': ['dominant_generic_residueDegree_functionField', 'curve_generic_height_preserved', 'complete_integral_curve_actual_cycle_projection'],
    'RealIntegralCurveProjection.lean': ['complete_integral_curve_real_cartier_projection'],
    'IntegralCurveProjection.lean': ['complete_integral_curve_cartier_projection'],
    'CurveRestrictionComposition.lean': ['dominant_curve_generic_unit_comp', 'generic_unit_transport_functionField', 'complete_normal_curve_cartier_intersection_reparametrization'],
    'CurveNormalizationLift.lean': ['birational_functionFieldMap_bijective', 'complete_integral_curves_normalization_lift_degree'],
    'NormalizationLift.lean': ['dominant_functionField_Spec_square', 'exists_finite_dominant_normalization_lift'],
    'RelativeNormalizationIdentification.lean': ['finite_dominant_generic_section_birational', 'finiteType_perfectField_relative_normalization_source_isIso'],
    'RelativeFieldNormalization.lean': ['finiteType_perfectField_relative_generic_normalization_isFinite'],
    'FiniteFunctionField.lean': ['finite_dominant_functionField_finite'],
    'NormalNormalization.lean': ['finiteType_perfectField_normal_normalization_isIso'],
    'FiniteFrobenius.lean': ['frobenius_isIntegral', 'finiteType_perfectField_frobenius_finite', 'finiteType_perfectField_iterateFrobenius_finite'],
    'FrobeniusIntegralClosure.lean': ['finiteType_perfectField_integralClosure_purelyInseparable_finite'],
    'PerfectIntegralClosure.lean': ['finiteType_perfectField_normal_integralClosure_finite'],
    'FiniteNormalizationAlgebra.lean': ['finiteType_perfectField_integralClosure_finite'],
    'RelativeIntegralClosureFinite.lean': ['finiteType_perfectField_relative_integralClosure_finite'],
    'FiniteNormalizationGeometry.lean': ['generic_stalk_preimage_nonempty_open', 'generic_stalk_affine_functionField_embedding', 'finiteType_perfectField_normalization_isFinite'],
    'GenericNormalizationNormal.lean': ['relative_integralClosure_isIntegrallyClosed', 'generic_normalization_affine_sections_normal', 'generic_normalization_stalks_normal'],
    'GenericNormalizationBirational.lean': ['finiteType_perfectField_normalization_birational'],
    'CurveNormalization.lean': ['generic_normalization_dimension_le_one', 'finiteType_perfectField_normalization_surjective', 'complete_integral_curve_normalization_properties'],
    'NormalizedCurveIntersection.lean': ['complete_integral_curve_real_intersection_point_image_zero', 'complete_integral_curve_real_cartier_presentation_independent'],
    'NormalizedIntersectionSigns.lean': ['complete_integral_curve_effective_real_intersection_signs'],
    'NormalizedIntersectionPullback.lean': ['exists_complete_integral_curve_real_intersection_pullback'],
    'FunctionFieldFunctoriality.lean': ['dominantFunctionFieldMap_comp'],
    'NormalizedCurveDegree.lean': ['complete_integral_curve_cartier_intersection_degree'],
    'NormalizedRealDegree.lean': ['complete_integral_curve_real_cartier_intersection_degree'],
    'AmbientCartierMoving.lean': ['movedCartierRestrictionData_rationalTwist', 'complete_normal_curve_ambient_cartier_principal_invariance'],
    'CartierZeroIntersection.lean': ['cartier_support_empty_of_coefficients_zero', 'cartierTotalOrder_zero_of_support_empty', 'complete_normal_curve_zero_cartier_intersection'],
    'CurveCartierCombinations.lean': ['moved_restriction_equation_on_chart', 'integral_combination_moved_local_units', 'exists_complete_curve_cartier_intersection_integralCombination'],
    'RealCurveIntersection.lean': ['complete_normal_curve_cartier_integral_relation', 'complete_normal_curve_cartier_rational_relation', 'complete_normal_curve_cartier_real_relation', 'complete_normal_curve_real_cartier_intersection_wellDefined'],
    'CartierReindex.lean': ['cartierAtlas_pointIndexed_coefficient', 'complete_normal_curve_cartier_intersection_pointIndexed'],
    'RealIntersectionPresentations.lean': ['complete_normal_curve_real_cartier_presentation_independent'],
    'EffectiveRealIntersection.lean': ['complete_normal_curve_effective_real_cartier_intersection_signs'],
    'CurveIntersectionPullback.lean': ['curve_generic_stalk_pullback_comp', 'exists_complete_curve_cartier_intersection_pullback'],
    'RealIntersectionPullback.lean': ['complete_normal_curve_real_cartier_intersection_point_image_zero', 'exists_complete_curve_real_cartier_intersection_pullback'],
    'CurvePointImageDegree.lean': ['cartierTotalOrder_zero_of_equations_one', 'constant_image_moved_cartier_restriction_degree_zero'],
    'CurveMoveDegree.lean': ['moved_cartier_restriction_ratio_equations', 'complete_normal_curve_moved_restriction_degree_independent'],
    'CartierCurveIntersection.lean': ['complete_normal_curve_cartier_intersection_eq_restriction', 'complete_normal_curve_cartier_intersection_wellDefined'],
    'EffectiveCurveIntersection.lean': ['effective_cartier_restriction_with_data', 'complete_normal_curve_effective_cartier_intersection_signs'],
    'CurveIntersectionDegree.lean': ['generic_stalk_functionField_self', 'genericPoint_not_cartier_support', 'dominant_moved_restriction_equations', 'complete_normal_curve_cartier_intersection_degree'],
    'AffineCurveOrders.lean': ['normal_curve_affine_dedekind', 'curve_affine_prime_coheight', 'normal_curve_affine_prime_order'],
    'FiniteCurveOrders.lean': ['finite_curve_chart_generic_tower', 'dominant_curve_chart_torsionFree', 'finite_normal_curve_fiber_order_degree'],
    'CurveFiberPrimes.lean': ['curve_chart_point_mem', 'curve_primeOver_maps_to_fiber', 'curve_fiber_point_prime_liesOver', 'curve_fiber_primes_actual_bijective'],
    'CurveClosedResidue.lean': ['curve_chart_base_scalar_tower', 'curve_chart_base_finiteType', 'finite_normal_curve_relative_residueDegree_one'],
    'CurveFiberDegree.lean': ['finite_normal_curve_unweighted_order_degree', 'finite_normal_curve_actual_fiber_order_degree'],
    'FiniteCurvePoints.lean': ['curve_affine_point_heightOne', 'finite_dominant_curve_preimage_nonempty', 'finite_normal_curve_maps_coheight_one'],
    'CurveCartierFiber.lean': ['finite_normal_curve_cartier_fiber_orders'],
    'CurveCartierDegree.lean': ['finsupp_mapDomain_actual_fiber', 'finite_normal_curve_cartier_push_pull', 'finite_normal_curve_cartier_pullback_degree'],
    'ProperCurveFinite.lean': ['curve_coheight_zero_generic', 'curve_nonGeneric_coheight_one', 'curve_genericPoint_not_closed', 'proper_dominant_curve_fibers_finite', 'proper_dominant_integral_curve_isFinite'],
    'ProperCurveCartierDegree.lean': ['complete_normal_curve_finite_cartier_pullback_degree', 'complete_normal_curve_cartier_pullback_degree'],
    'SeparatingParameter.lean': ['exists_finite_separable_transcendental_parameter', 'exists_compatible_finite_separable_ratFunc_embedding'],
    'AffineCurveFunctionField.lean': ['integral_subring_krullDimLE_one', 'affine_curve_ring_trdeg_one', 'affine_curve_fractionField_finiteType_trdeg_one'],
    'CurveFunctionField.lean': ['curve_affine_chart_dimension', 'curve_affine_chart_not_field', 'curve_affine_constants_compatible', 'curve_functionField_properties_of_closed_point', 'curve_exists_coheight_one', 'finiteType_curve_exists_separating_parameter'],
    'CurveProductFormula.lean': ['complete_normal_curve_principal_product_formula'],
    'CartierDegreeInvariance.lean': ['complete_normal_curve_cartier_degree_invariant'],
    'DedekindValuationPlaces.lean': ['valuation_fraction_mem_of_unit_denominator', 'valuation_chart_center_nonzero', 'dedekind_chart_valuation_unique_prime'],
    'ValuationChartCover.lean': ['valuation_constants_trivial', 'integral_element_mem_valuation', 'rational_infinity_ring_mem_of_parameter_pole', 'functionField_valuation_integralClosure_chart_cover'],
    'FunctionFieldValuationPlaces.lean': ['finite_place_parameter_regular', 'infinity_place_parameter_pole', 'twoChartValuation_injective', 'twoChartValuation_ne_top', 'twoChartValuation_contains_constants', 'functionField_valuation_unique_twoChart_place'],
    'DvrAdicOrders.lean': ['dvr_heightOneOrder_regular', 'dvr_heightOneOrder_eq_rationalOrder', 'dedekind_prime_order_eq_valuationRing_order'],
    'CurveChartPlaces.lean': ['curve_twoChart_center_exists', 'curveTwoChartCenter_valuation', 'proper_normal_curve_twoChart_centers_bijective'],
    'CurvePrincipalDegree.lean': ['dedekind_prime_actual_curve_order', 'twoChartPrincipalDivisor_actual_order', 'curvePrincipalDivisor_coefficient', 'proper_normal_curve_principal_degree_zero'],
    'CartierPrincipalDegree.lean': ['curvePrincipalDivisor_allPoints_coefficient', 'cartierOrderDivisor_rationalTwist', 'cartierTotalOrder_rationalTwist'],
    'RationalInfinityResidue.lean': ['rational_infinity_approximate_constant', 'rational_infinity_residue_constants_bijective', 'rational_infinity_residue_degree_one', 'rational_infinity_inertia_degree_one', 'infinity_pushforward_degree', 'twoChart_baseField_principal_degree_zero', 'algebraicallyClosed_infinity_point_degree_one', 'affineDivisorDegree_eq_order_sum'],
    'FunctionFieldDegree.lean': ['functionField_principal_degree_baseField_zero', 'functionField_principal_order_sum_zero'],
    'ValuationCenters.lean': ['curveFunctionFieldBaseMap_spec', 'local_valuation_fractionRing_bijective', 'valuation_generic_lift_over_base', 'proper_functionField_valuation_unique_lift', 'valuation_center_stalk_functionField_compat', 'valuation_center_stalk_bijective', 'normal_curve_stalk_isValuation', 'nontrivial_valuation_center_coheight_one', 'curve_coheight_one_isClosed', 'proper_normal_curve_unique_valuation_center_iso'],
    'NormalCurveValuations.lean': ['normalCurvePointValuation_ne_top', 'normalCurvePointValuation_contains_constants', 'normalCurvePointValuation_center_eq', 'normalCurvePointValuation_lift', 'normalCurvePointValuation_injective', 'proper_normal_curve_valuation_has_closed_point', 'proper_normal_curve_points_valuations_bijective'],
    'ValuationOrderTransport.lean': ['dvr_rationalOrder_commonField_ringEquiv', 'normal_curve_valuation_center_order', 'proper_normal_curve_valuation_order_correspondence'],
    'NormDivisor.lean': ['separable_relNorm_factorization', 'ideal_primePower_multiplicity', 'ideal_primePower_product_multiplicity', 'normalizedIdealPoints_asIdeal', 'separable_ideal_norm_order', 'heightOneOrder_regular_eq_multiplicity', 'separable_integral_norm_order', 'ideal_order_eq_point_count', 'idealFactorDivisor_apply', 'idealFactorDivisor_principal', 'affineDivisorPushforward_single', 'separable_ideal_norm_divisor', 'fractionFieldNormUnits_integral', 'separable_integral_principal_norm', 'separable_affine_principal_norm', 'affineDivisorPushforward_degree', 'separable_affine_principal_norm_degree', 'fractionRing_separable_of_fractionFields', 'separable_integral_functionField_norm', 'separable_functionField_principal_norm', 'separable_functionField_principal_norm_degree'],
    'RationalDivisor.lean': ['polynomial_point_residueDegree', 'polynomial_prime_principal_divisor', 'polynomial_prime_principal_degree', 'polynomial_principal_degree', 'rational_affine_principal_degree', 'rational_actual_principal_degree_zero'],
    'InfinityNorm.lean': ['normalized_discrete_valuation_eq', 'rational_infinity_normalized_valuation', 'rational_infinity_heightOneOrder', 'separable_infinity_principal_norm', 'twoChart_principal_degree_zero'],
    'FunctionFieldProductFormula.lean': ['functionField_principal_degree_zero'],
    'CartierDegree.lean': ['cartierOrderDivisor_apply', 'cartierTotalOrder_eq_of_unit_transitions', 'effective_cartierTotalOrder_nonneg', 'effective_cartierTotalOrder_pos', 'effective_cartierTotalOrder_pos_of_support'],
    'CartierCurveRestriction.lean': ['stalkSpecialization_functionField', 'generic_stalkMap_commutes', 'exists_cartierAtlas_nondominant_pullback', 'exists_effective_nondominant_cartier_pullback', 'effective_cartier_restriction_order_signs'],
    'RealCartierCurveDegree.lean': ['effective_real_cartier_curve_order_signs', 'effective_realCartier_curve_decomposition_order_signs'],
    'CartierCurveMoving.lean': ['cartierAtlas_move_off_generic_curve', 'cartierAtlas_rationalTwist_transition', 'exists_moved_cartier_curve_restriction'],
    'RealCartierPullback.lean': ['dominantFunctionFieldMap_stalk_unit', 'cartierAtlas_pullback_coefficient_eq', 'cartierAtlas_integralCombination_coefficients', 'exists_realCartier_effective_decomposition_equations', 'cartierAtlas_pullback_integralCombination_coefficients', 'realWeightedWeilCycle_eq_of_integral_coefficients', 'exists_effective_cartierAtlas_pullback_data', 'exists_realCartier_termwise_pullback_support', 'exists_realCartier_termwise_fiber_descent'],
    'NormalExtension.lean': ['normal_local_annihilator_maximal_isPrincipal', 'normal_local_associated_principal_maximal_isPrincipal', 'normal_local_associated_principal_isDVR', 'normal_principal_associated_prime_isDVR', 'normal_principal_associated_prime_height_one', 'normal_divisibility_of_height_one_local', 'normal_fraction_regular_iff_height_one', 'normal_fraction_regular_of_height_one_denominators'],
    'CartierEffectivity.lean': ['dvr_rationalOrder_nonneg_iff_regular', 'normal_affine_rational_regular', 'cartierAtlas_effective_iff_weil_nonneg', 'exists_realCartier_effective_weil_decomposition'],
    'CartierVanishing.lean': ['rationalUnitAt_exists_affine_unit_section', 'rationalUnitAt_isOpen', 'cartierAtlas_vanishingSupport_isClosed', 'normal_affine_rationalUnitAt_of_orders_zero', 'cartierAtlas_vanishingSupport_eq_closure_weilSupport', 'effective_cartier_real_sum_support', 'exists_effective_real_sum_pullback_support', 'exists_realCartier_decomposition_support_pullback'],
    'RationalCone.lean': ['open_set_mem_convexHull_rational', 'open_set_exists_rational_convex_combination', 'positive_rational_coefficient_decomposition', 'rational_parameterization_preserves_zero', 'rationalCoefficientMap_cast', 'rationalCoefficientMap_comp_zero', 'effective_rational_coefficient_decomposition', 'rational_vector_positive_integer_multiple', 'effective_integral_coefficient_decomposition'],
    'CartierCombinations.lean': ['dvr_rationalOrder_zpow', 'dvr_rationalOrder_prod', 'exists_cartierAtlas_integralCombination', 'exists_cartierAtlas_integralCombination_coefficients'],
    'RealCartierDecomposition.lean': ['exists_realCartier_nonnegative_weil_decomposition'],
    'FiniteNormalGeometry.lean': ['birationalMorphism_dominant', 'birationalMorphism_generic_stalk_isIso', 'dominantFunctionFieldMap_germ', 'finite_normal_birational_affine_bijective', 'finite_normal_birational_isIso', 'normalStalks_restrict', 'birationalMorphism_restrict', 'proper_normal_birational_isIso_near_finite_fiber', 'birational_affine_functionField_embedding', 'birational_relative_integralClosure_bijective', 'normal_birational_fromNormalization_isIso', 'proper_normal_birational_isIso_near_quasiFiniteAt', 'exceptional_point_not_quasiFiniteAt', 'exceptional_fiber_point_not_isOpen_singleton'],
    'CartierSupport.lean': ['rationalUnitAt_unit_transition', 'cartierAtlas_support_eq_on_chart', 'rationalUnitAt_regular_iff', 'rationalUnitAt_regular_pullback_iff', 'exists_effective_cartierAtlas_pullback_support', 'effective_cartierAtlas_weil_nonneg', 'exists_effective_cartierAtlas_fiber_descent'],
    'DivisorPullback.lean': ['affineDivisorDegree_single', 'affinePointDivisorPullback_degree', 'affineDivisorPullback_degree', 'affinePointDivisorPullback_apply', 'affineDivisorPullback_apply', 'affinePrincipalDivisor_pullback', 'closedPoint_residueDegree_one', 'algebraicallyClosed_point_pullback_count', 'affineDivisorPullback_support', 'affineDivisorPullback_effective_iff', 'algebraicallyClosed_effective_divisor_degree_pos'],
    'SeparableNorm.lean': ['separable_prime_ideal_norm'],
    'StrictTransform.lean': ['geometricStrictTransform_image', 'geometricStrictTransform_injective', 'geometric_exceptional_iff', 'scheme_cycle_strictTransform_coefficient', 'weilCycleCoefficients_pushforward'],
    'CartierPushPull.lean': ['proper_birational_weil_cycle_pushforward', 'exists_cartierAtlas_pullback_pushforward', 'cartierAtlas_real_sum_isWeilDivisor', 'exists_realCartier_pullback_pushforward', 'exists_realCartier_effectivity_descent'],
    'CartierPullback.lean': ['dominant_genericPoint_eq', 'dominantFunctionFieldMap_stalk', 'exists_cartierAtlas_pullback', 'dominantFunctionFieldMap_order_of_stalk_iso'],
    'CartierAtlas.lean': ['cartierAtlas_order_agrees', 'schemeRationalOrder_zero_of_unit_germs', 'finite_schemeRationalOrder_on_affine', 'cartierAtlas_coefficient_eq', 'cartierAtlas_locallyFiniteSupport', 'cartierAtlas_weilCycle_isWeilDivisor', 'cartierAtlas_weilCycle_eq_of_unit_transitions', 'cartierAtlas_weilCycle_finite_support'],
    'CodimensionSupport.lean': ['finite_heightOne_primes_containing', 'finite_codimensionOne_nonunit_germs'],
    'FractionFieldOrders.lean': ['dvr_rationalOrder_represents', 'dvr_rationalOrder_unit', 'dvr_rationalOrder_mul', 'dvr_rationalOrder_unit_transition'],
    'CodimensionOne.lean': ['generic_stalk_dominant', 'normal_codimensionOne_stalk_isDVR', 'separated_dominant_section_isIso', 'proper_birational_isIso_near_DVR', 'proper_birational_isIso_near_codimensionOne', 'proper_birational_isIso_on_codimensionOne_open', 'stalkMap_isIso_over_isomorphism_open', 'proper_birational_codimensionOne_unique_preimage', 'proper_birational_surjective'],
    'HartshorneGraph.lean': ['isIso_over_dense_open_section', 'hartshorne_graph_closure'],
    'RelativeNumerics.lean': ['relative_nef_neg_iff', 'relative_curvePositive_neg_iff'],
    'RationalProductFormula.lean': ['polynomial_factor_degree_sum', 'rationalInfinityOrder_eq', 'rationalFunction_principal_degree_zero'],
    'NormalSections.lean': ['normal_affine_sections'],
    'PointPullback.lean': ['point_pullback_tensor_iso', 'point_pullback_tensor_length', 'finite_flat_point_pullback_degree', 'finite_flat_point_pullback_degree_over_base'],
    'CurveSelection.lean': ['exists_closedPoint_outside_support', 'finiteType_exists_closedPoint_outside_support'],
    'LocalConnectedness.lean': ['localRing_idempotent_trivial', 'localRing_not_product_nontrivial'],

    'CurveDegree.lean': ['finite_flat_fiber_degree', 'finite_flat_signed_point_degree', 'finite_flat_fiber_functionField_degree', 'heightOneOrder_mul', 'heightOneOrder_pullback', 'finite_flat_order_fiber_degree'],
    'PrincipalDivisors.lean': ['heightOneOrder_finite_support', 'affinePrincipalDivisor_apply', 'affinePrincipalDivisor_mul', 'heightOneOrder_regular_unit', 'affinePrincipalDivisor_unit_transition', 'heightOneOrder_nonneg_iff', 'affinePrincipalDivisor_effective_iff', 'affinePrincipalDivisor_inv', 'affinePrincipalDivisor_eq_zero_iff'],
    'PullbackDiagram.lean': ['curve_square_pullback_iso'],

    'AffineSections.lean': ['affine_quasicoherent_exists_nonzero_section'],
    'NormalBirational.lean': ['integral_birational_algebraMap_bijective', 'finite_birational_algebraMap_bijective', 'finite_birational_spec_isIso'],
    'LocalGeometry.lean': ['normal_one_dimensional_local_isDVR', 'scheme_normal_one_dimensional_stalk_isDVR', 'proper_dvr_lift', 'proper_valuative_lift_unique', 'proper_quasiFinite_isFinite', 'proper_finite_fiber_neighborhood'],
    'LocalPushPull.lean': ['dvr_order_ringEquiv', 'dvr_fraction_order_well_defined', 'dvr_fraction_order_ringEquiv', 'scheme_pushpull_of_local_coefficients', 'scheme_stalk_fraction_order_of_iso', 'scheme_residueDegree_of_iso', 'scheme_residueDegree_of_stalk_iso', 'scheme_pushpull_of_local_isomorphisms'],
    'Projection.lean': ['scheme_cycle_map_single', 'scheme_curve_push_of_same_weight', 'scheme_curve_push_of_drop', 'projection_cases_from_cycle_push', 'nonpositive_pullback_from_cycle_push', 'projection_formula_on_real_span', 'scheme_effective_descends'],
    'GeometricCycles.lean': ['scheme_cycle_map_effective', 'scheme_mapCoeff_zero_of_drop', 'scheme_mapCoeff_of_same_weight', 'scheme_cycle_map_zero_of_drop'],
    'Numerical.lean': ['exists_effective_shift', 'effective_of_curve_tests'],
    'Coefficients.lean': ['effective_push', 'negative_is_exceptional', 'exists_least_effective_shift'],
    'Descent.lean': ['push_comp', 'push_zero_iff_exceptional_support', 'effective_both_signs_iff_zero', 'nonpositive_smul', 'nonpositive_pullback', 'effective_descends', 'negativity_descends', 'subset_iff_preimage_subset', 'disjoint_iff_preimage_disjoint', 'support_dichotomy_descends', 'composite_fiber', 'fiber_dichotomy_descends', 'push_embDomain', 'push_add_exceptional', 'effective_descends_coefficients'],
    'Interfaces.lean': ['effective_iff_push_effective', 'exceptional_subset_support', 'fiber_support_dichotomy'],
}
logs = []
for args in [['lake', 'build'], ['lake', 'env', 'lean', 'CheckAxioms.lean']]:
    result = subprocess.run(args, cwd=project, capture_output=True, text=True, encoding='utf-8', check=True)
    logs.append('$ ' + ' '.join(args) + '\n' + result.stdout + result.stderr)
audit = logs[1]
axiom_records = {}
for name in sum(names.values(), []):
    match = re.search(r"'Negativity\." + name + r"' depends on axioms: \[(.*?)\]", audit, re.S)
    if match:
        actual = [a.strip() for a in match.group(1).split(',') if a.strip()]
    elif "'Negativity." + name + "' does not depend on any axioms" in audit:
        actual = []
    else:
        raise RuntimeError('Missing axiom record: ' + name)
    if not set(actual) <= {'propext', 'Classical.choice', 'Quot.sound'}:
        raise RuntimeError('Unexpected axioms: ' + name + str(actual))
    axiom_records[name] = actual
if 'sorryAx' in audit:
    raise RuntimeError('Unproved axiom detected')
source = destination / 'source'
source.mkdir(parents=True, exist_ok=True)
files = ['Negativity.lean', 'CheckAxioms.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'THIRD_PARTY_NOTICES.txt']
files += ['Negativity/' + n for n in ['Basic.lean', *names]]
files += [p.relative_to(project).as_posix() for p in sorted(
    (project / 'Negativity/External/Laurent').rglob('*')) if p.is_file()]
manifest = []
for relative in files:
    data = (project / relative).read_bytes()
    if relative.endswith('.lean') and re.search(r'\b(sorry|admit|axiom)\b', data.decode('utf-8-sig')):
        raise RuntimeError('Unexpected placeholder: ' + relative)
    target = source / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    record = {'path': relative, 'sha256': hashlib.sha256(data).hexdigest()}
    if relative.endswith('.lean'):
        record['lineCount'] = len(data.decode('utf-8-sig').splitlines())
    manifest.append(record)
declarations = {}
for filename, declarations_in_file in names.items():
    code = (project / 'Negativity' / filename).read_text(encoding='utf-8-sig')
    for name in declarations_in_file:
        match = re.search(r'^theorem ' + name + r'\b', code, re.M)
        if not match:
            raise RuntimeError('Missing declaration ' + name)
        remainder = code[match.start():]
        end = re.search(r'\n(?:/--|theorem |end Negativity|@\[)', remainder)
        snippet = remainder[:end.start() if end else len(remainder)].strip()
        declarations[name] = {'path': 'Negativity/' + filename, 'line': code[:match.start()].count('\n') + 1, 'code': snippet, 'axioms': axiom_records[name]}
mathlib = next(p['rev'] for p in json.loads((project / 'lake-manifest.json').read_text(encoding='utf-8-sig'))['packages'] if p['name'] == 'mathlib')
date = datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat(timespec='seconds')
snapshot = {'schemaVersion': 1, 'checkedAt': date, 'lean': (project / 'lean-toolchain').read_text().strip(), 'mathlib': mathlib, 'files': manifest, 'declarations': declarations, 'graphEdges': 'manually curated mathematical blueprint; not a kernel dependency dump', 'verification': 'local lake build and #print axioms; not browser-side verification'}
(destination / 'snapshot.json').write_text(json.dumps(snapshot, ensure_ascii=False, indent=2), encoding='utf-8')
(destination / 'verification.txt').write_text('Verified ' + date + '\n\n' + '\n'.join(line.rstrip() for log in logs for line in log.splitlines()), encoding='utf-8')
readme = '''Negativity: coefficient core and conditional interfaces

This snapshot is NOT a complete geometric proof of the negativity lemma.
New algebraic norm/valuation and actual Cartier restriction/order proofs
are included. Hartshorne I.6 actual curve-point/valuation bijection and local-order
transport, exhaustive disjoint finite/infinity place classification, actual
curve principal degree zero, and Cartier principal-move degree independence
are proved; the compatible finite separable parameter is now constructed
from actual finite-type one-dimensional Scheme geometry. Actual complete
normal curves have principal degree zero and Cartier principal-move invariance
without a parameter input, in arbitrary characteristic. Actual global Cartier pullback degree for proper dominant complete normal
curves, including inseparable maps, is proved with actual fibers and
local equations. Actual Cartier curve intersection is now constructed; its
rational-move independence, contracted-curve zero, effective-divisor signs
and proper dominant curve degree formula are proved. Actual ambient principal
moving, zero-Weil intersection, integer additivity, arbitrary real-presentation
independence (including different generators and covers), effective real-divisor
intersection signs, and actual ambient Cartier/R-Cartier pullback composition
are now proved. The integral closure of every finite-type perfect-field domain
in any finite function-field extension is proved finite, including inseparable
extensions. Actual Scheme normalization is proved finite, birational and normal.
For complete integral curves its properness, surjectivity and dimension one are
derived. Actual Cartier/R-Cartier intersection on nonnormal complete source curves,
arbitrary real-presentation independence, effective-divisor signs, point-image
zero and ambient pullback composition are proved on the constructed normalization.
The degree formula for nonnormal source curves and normal target curves uses
the original full function-field degree. Actual finite dominant maps induce
finite function-field extensions. Relative normalization in the actual source
function field is finite and equals any actual normal finite dominant source.
Actual finite dominant lifting to a nonnormal target's normalization is proved.
Every proper dominant map between complete integral curves, with neither curve
normal or smooth, has an actual finite dominant normalization lift, a commuting
square and unchanged full function-field degree. Local Cartier restriction compatibility along actual proper dominant maps is
proved without requiring the ambient curve embedding to be dominant. Actual
Cartier and arbitrary real Cartier projection formulas hold for maps between
complete integral curves, neither normal nor smooth. Actual fundamental-cycle
pushforward uses dimension weights and generic residue-field degrees, and its
compatibility with this intersection is proved without an intersection identity
input. Actual image integrality, properness and dimension alternatives are
proved. The full ambient Cartier/R-Cartier projection formula is now proved,
including actual embedded curves, actual ambient cycle pushforward, point-image
zero and full inseparable degree. A single actual Cartier pullback is fixed
independently of all test curves; its real intersection composition is proved
for every complete integral curve. Relative nefness is defined on actual
contracted complete curves using the constructed intersection, and actual
dominant pullback preserves it without an assumed geometric compatibility or
nef-transport identity. Actual exceptional closed-point curve coverage is now constructed over any
algebraically closed field: Noether normalization and going-down build an
affine integral curve through a prescribed point, actual scheme closure makes
it complete, and actual Zariski main theorem places it in the contracted
fiber. For an effective actual real Cartier divisor with zero coefficient at
an exceptional prime, the support-outside closed point, contracted complete
curve and nonnegative actual intersection are all constructed; no curve
existence input is assumed. Actual cycle pushforward preserves coefficients over every actual isomorphism
open. Effectivity of the actual pushforward therefore places every negative
coefficient over the actual exceptional center. The full maximum-ratio
contradiction is now proved on actual Cartier presentations, actual contracted
curves and actual intersection, with only the supplied E witness's effectivity,
exceptional coverage and strict negative contracted-curve degrees as additional
inputs. It does not construct E or derive geometric ample positivity; this is
still a conditional first-part result, NOT the full negativity lemma.
High-dimensional curve selection is now actually constructed: a line
through a prescribed polynomial zero avoiding that zero set, an actual
one-dimensional prime quotient with avoidance, and its actual complete
scheme closure. Every nonempty proper closed subset of an actual connected
proper scheme, including reducible and nonreduced schemes, is met by an actual
complete integral curve not contained in it. Actual support dichotomy for
effective real Cartier divisors with negative relative nefness is proved on
connected complete contracted schemes, with no curve-existence or positive-
intersection input. Connectedness of actual proper birational fibers is NOT
proved by this result and remains open.
Actual effective E construction by clearing base-ring denominators is now
proved for every actual Cartier divisor over an affine birational base.
Principal changes preserve the actual normalized intersection. Strictly
anti-positive Cartier data yield a constructed effective E covering all
actual exceptional primes, with neither E effectivity nor coverage as an
input. Actual affine nonvanishing section-cover geometry implies positive
intersection on complete closed curves: a proper integral curve cannot lie
inside an affine open. Negativity (1) is proved given actual Cartier affine
section-cover data, with no supplied numerical positivity or E witness.
Actual Proj coordinate ratios, stalk units and germs, their closed-embedding
pullbacks, Cartier transitions, effective coordinate sections and affine
nonvanishing loci are now constructed and proved. Standard polynomial
degree-one generators supply the cover without additional section data.
Actual projective-affine negativity (1) is proved for arbitrary real
Cartier presentations over an affine normal base, with an actual closed
embedding into standard relative projective space. No Cartier section,
effective E, exceptional coverage or numerical positivity witness is an
input. E itself is also constructed in a separate actual existence theorem.
Global affine-base gluing is now proved: fixed actual Cartier restrictions
preserve local orders, actual pushforward effectivity restricts, and actual
relative nefness restricts with genuine normalized intersections. The
relative projective interface consists of actual closed Proj embeddings
commuting with the base morphism. Actual real-Cartier projective negativity
(1), including both effectivity directions, is proved on a general normal
base. No affine-base, divisor, section, E, numerical or local-effectivity
witness is assumed. The projective result is now subsumed by actual proper negativity (1).
Hartshorne's finite affine cover and actual projective-chart immersions,
actual graph image, proper birational surjective graph projection and
finite projection to a constructed finite projective product are proved.
The actual finite normalization gives an actual normal modification.
Product coordinate ratios construct an actual Cartier affine-section
cover on this modification, without an O(1), effective-section or
positive-degree witness. Canonical actual Cartier push-pull, actual
birational cycle composition and actual nef pullback perform descent.
Actual proper real-Cartier negativity (1), including D>=0 iff f_*D>=0,
is now proved over a general normal base in arbitrary characteristic,
with no projectivity, modification, section, E or curve input.
Actual proper birational fiber connectedness and therefore conclusion
(2) remain open. The complete two-part theorem is NOT yet proved.
The actual natural structure-sheaf map O_Y -> f_*O_X of a proper
birational morphism to a normal locally Noetherian integral base is now
proved to be an isomorphism, by actual codimension-one extension and
sheaf gluing. Actual functions descend on every open, including
nonaffine and empty opens. Actual clopen decompositions construct
characteristic sections and nontrivial idempotents; their genuine
pullbacks are compatible. Actual ideal-power thickenings and their
actual inverse-limit section ring are constructed, and a disconnected
closed subscheme produces a compatible nontrivial idempotent in that
ring. The canonical actual affine formal-functions comparison with
adic completion is proved bijective. This last theorem requires the
source scheme itself to be affine: it does not establish the proper
nonaffine global formal-functions comparison needed for actual fiber
connectedness. The complete proper two-part target remains open.
The geometric input needed from Hartshorne's modification for proper
negativity (1) is complete. This does not claim a separately formalized
Segre embedding or the general relative-projective Chow theorem.
The remaining main-target gap is actual proper birational fiber
connectedness via the proper nonaffine global formal-functions comparison.
The independent fiber-support conclusion (2) and full two-part theorem
remain open.
The canonical relative formal-functions map is now constructed with an
affine base and an arbitrary nonaffine source, using actual comapped ideal
powers and actual scheme pullbacks. A disconnected actual closed-point
fiber constructs a compatible nontrivial idempotent in its actual section
limit. The base completion is local without requiring the original affine
base ring to be local. Bijectivity of this precise constructed comparison
would therefore give actual closed-fiber connectedness. Actual proper birational geometry over an affine finite-type integral
base over a perfect field now proves a uniform kernel bound, including
the zero-ideal case. Actual valuative lifts prove homogeneous integrality
over the Rees algebra, finite normalization gives a finite graded kernel
module, and filtration stability supplies the uniform shift. The actual
relative comparison is therefore proved injective for a nonaffine source.
SURJECTIVITY is NOT proved. Actual affine-cover Cech cohomology is now constructed with actual
structure-sheaf gluing, local closed-immersion lifts, choice-independent
connecting classes, genuine transition naturality and two exactness
statements. The actual global-section module action is proved. Properness
constructs a finite affine cover with affine intersections. A uniform
actual first-cohomology kernel-transition vanishing bound would construct
the actual section lifts and prove actual formal-functions bijectivity.
This bound is NOT proved: proper graded cohomology finite generation and
the resulting uniform kernel vanishing remain open. The missing actual
eventual image-lifting bound is still explicit; the full comparison and full second negativity
conclusion are NOT complete.
Actual closed fibers are proved proper over the ground field. A genuine
Chevalley/Jacobson constructible-locus argument proves that closed-fiber
support dichotomy implies the dichotomy on every fiber. Actual affine
neighborhood fiber homeomorphisms connect the local comparison to the
global closed-fiber statement. Both actual proper negativity conclusions
are now composed in a theorem with the single explicit remaining
ActualClosedFiberFormalFunctions hypothesis. This is a CONDITIONAL
two-part result, NOT completion of the actual full theorem. Conclusion
(1) remains independently fully proved without that hypothesis.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
The imported arbitrary-ring Laurent Cech finiteness and nonnegative-twist
vanishing proofs are reused from a pinned Apache-2.0 upstream project and
rebuilt with this toolchain. Their complete 17-file dependency chain,
license, provenance and adaptations are included in External/Laurent.
These are explicit-complex results: identification with actual projective
scheme/coherent-sheaf cohomology and proper graded finite generation remain
open. The upstream complete theorem over Q has not been independently
rebuilt here and does not establish arbitrary-characteristic properness.
Actual graded cocycle multiplication, quotient action and a genuine Rees
module structure on cocycles are also verified; finite generation is not
claimed.

Proof sources: see Negativity.lean for the complete module import list, and
CheckAxioms.lean / snapshot.json for the audited declarations and exact source locations.
'''
(source / 'README.txt').write_text(readme, encoding='utf-8')
with zipfile.ZipFile(destination / 'negativity-lean.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for f in sorted(source.rglob('*')):
        if f.is_file():
            archive.write(f, 'negativity/' + f.relative_to(source).as_posix())
print('Verified and exported', len(files), 'files and', len(declarations), 'declarations')
