"""Publish only project sources and verified evidence, never .lake or local user data."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys, zipfile

project, destination = map(Path, sys.argv[1:3])
names = {
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
Proof source: Negativity/Numerical.lean, Coefficients.lean, Interfaces.lean, Descent.lean, GeometricCycles.lean.
'''
(source / 'README.txt').write_text(readme, encoding='utf-8')
with zipfile.ZipFile(destination / 'negativity-lean.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for f in sorted(source.rglob('*')):
        if f.is_file():
            archive.write(f, 'negativity/' + f.relative_to(source).as_posix())
print('Verified and exported', len(files), 'files and', len(declarations), 'declarations')
