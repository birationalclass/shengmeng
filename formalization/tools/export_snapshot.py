"""Publish only project sources and verified evidence, never .lake or local user data."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, zipfile

project, destination = map(Path, sys.argv[1:3])
names = {
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
manifest = []
for relative in files:
    data = (project / relative).read_bytes()
    if relative.endswith('.lean') and re.search(r'\b(sorry|admit|axiom)\b', data.decode('utf-8-sig')):
        raise RuntimeError('Unexpected placeholder: ' + relative)
    target = source / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    manifest.append({'path': relative, 'sha256': hashlib.sha256(data).hexdigest()})
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
are included. Complete Scheme-curve place identification, principal-move
degree independence, geometric ample positivity, full Chow construction
and connected-fiber curve existence remain open.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
Proof source: Negativity/Numerical.lean, Coefficients.lean, Interfaces.lean, Descent.lean, GeometricCycles.lean, Projection.lean, LocalPushPull.lean, LocalGeometry.lean, NormalBirational.lean, AffineSections.lean, CurveDegree.lean, PrincipalDivisors.lean, PullbackDiagram.lean, PointPullback.lean, CurveSelection.lean, LocalConnectedness.lean, CodimensionOne.lean, HartshorneGraph.lean, RelativeNumerics.lean, RationalProductFormula.lean, NormalSections.lean, FractionFieldOrders.lean, CodimensionSupport.lean, CartierAtlas.lean, CartierPullback.lean, CartierPushPull.lean, StrictTransform.lean, DivisorPullback.lean, SeparableNorm.lean, FiniteNormalGeometry.lean, CartierSupport.lean, RationalCone.lean, CartierCombinations.lean, RealCartierDecomposition.lean, NormalExtension.lean, CartierEffectivity.lean, CartierVanishing.lean, RealCartierPullback.lean, NormDivisor.lean, RationalDivisor.lean, InfinityNorm.lean, FunctionFieldProductFormula.lean, CartierDegree.lean, CartierCurveRestriction.lean, RealCartierCurveDegree.lean, CartierCurveMoving.lean.
'''
(source / 'README.txt').write_text(readme, encoding='utf-8')
with zipfile.ZipFile(destination / 'negativity-lean.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for f in sorted(source.rglob('*')):
        if f.is_file():
            archive.write(f, 'negativity/' + f.relative_to(source).as_posix())
print('Verified and exported', len(files), 'files and', len(declarations), 'declarations')
