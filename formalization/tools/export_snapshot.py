"""Publish only project sources and verified evidence, never .lake or local user data."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, zipfile

project, destination = map(Path, sys.argv[1:3])
names = {
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
    match = re.search(r"'Negativity\." + name + r"' depends on axioms: \[(.*?)\]", audit)
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
files = ['Negativity.lean', 'CheckAxioms.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
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
(destination / 'verification.txt').write_text('Verified ' + date + '\n\n' + '\n'.join(logs), encoding='utf-8')
readme = '''Negativity: coefficient core and conditional interfaces

This snapshot is NOT a complete geometric proof of the negativity lemma.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
Proof source: Negativity/Numerical.lean, Coefficients.lean, Interfaces.lean, Descent.lean, GeometricCycles.lean, Projection.lean, LocalPushPull.lean, LocalGeometry.lean, NormalBirational.lean, AffineSections.lean, CurveDegree.lean, PrincipalDivisors.lean, PullbackDiagram.lean, PointPullback.lean, CurveSelection.lean, LocalConnectedness.lean, CodimensionOne.lean, HartshorneGraph.lean, RelativeNumerics.lean, RationalProductFormula.lean, NormalSections.lean, FractionFieldOrders.lean, CodimensionSupport.lean, CartierAtlas.lean, CartierPullback.lean, CartierPushPull.lean, StrictTransform.lean.
'''
(source / 'README.txt').write_text(readme, encoding='utf-8')
with zipfile.ZipFile(destination / 'negativity-lean.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for f in sorted(source.rglob('*')):
        if f.is_file():
            archive.write(f, 'negativity/' + f.relative_to(source).as_posix())
print('Verified and exported', len(files), 'files and', len(declarations), 'declarations')
