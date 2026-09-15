"""Rebuild the finite lower-bound certificate (Python 3, SymPy 1.14.0, Node).

RUBIK_NODE=/path/to/node python3 generate-certificate.py
SymPy discovers short straight-line programs; the independent JS verifier only
checks products, fixed points and finite orbits, and does not trust SymPy.
"""
import json
import os
import subprocess
from pathlib import Path
from functools import reduce
from sympy.combinatorics import Permutation, PermutationGroup

HERE = Path(__file__).resolve().parent
raw = subprocess.check_output([os.environ.get('RUBIK_NODE', 'node'), '--input-type=module', '-e', """
import * as C from './cube-core.mjs';
console.log(JSON.stringify({faces:C.FACES,generators:C.FACES.map(f=>C.mobilePermutation(C.MOVES[f])),base:[...C.CORNER_SLOTS.slice(0,7),...C.EDGE_SLOTS.slice(0,11)].map(s=>C.MOBILE.indexOf(s[0]))}));
"""], cwd=HERE, text=True)
data = json.loads(raw)
original = [Permutation(a) for a in data['generators']]
base, strong, slps = PermutationGroup(original).schreier_sims_incremental(base=data['base'], slp_dict=True)
nodes = [['move', face] for face in data['faces']]
known = {g: i for i, g in enumerate(original)}
values = original[:]

def reference(g):
    if g in known:
        return known[g]
    gi = g**-1
    assert gi in known, 'Every word must reference an earlier generator.'
    node = len(nodes)
    nodes.append(['inverse', known[gi]])
    known[g] = node
    values.append(g)
    return node

for g in strong[len(original):]:
    # SymPy's SLP is stored in right-multiplication order, i.e. reversed here.
    refs = [reference(h) for h in reversed(slps[g])]
    product = reduce(lambda a, b: a*b, [values[i] for i in refs], Permutation(list(range(48))))
    assert product == g
    known[g] = len(nodes)
    nodes.append(['word', refs])
    values.append(g)

levels = []
for i, point in enumerate(base):
    refs = [known[g] for g in strong if all(g(b) == b for b in base[:i])]
    orbit = {point}
    queue = [point]
    for x in queue:
        for ref in refs:
            y = values[ref](x)
            if y not in orbit:
                orbit.add(y)
                queue.append(y)
    levels.append({'point': point, 'generators': refs, 'orbitSize': len(orbit)})

certificate = {'format': 'rubik-orbit-lower-bound-v1', 'convention': 'left-to-right', 'degree': 48, 'nodes': nodes, 'levels': levels}
(HERE / 'certificate.json').write_text(json.dumps(certificate, separators=(',', ':'))+'\n')
print('Nodes:', len(nodes), 'Orbit sizes:', [level['orbitSize'] for level in levels])
