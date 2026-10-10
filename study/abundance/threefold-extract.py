import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
stem = 'nef-abundance-threefold-behavior-20261010'
raw = (ROOT / (stem + '.tex')).read_bytes()
text = raw.decode('utf-8').replace('\r\n', '\n')
body = text.split(r'\maketitle', 1)[1].rsplit(r'\end{document}', 1)[0]
pattern = re.compile(r'\\(?P<heading>section|subsection)\{(?P<title>[^{}]*)\}|'
                     r'\\begin\{(?P<kind>theorem|setup|lemma|proposition|corollary|proof|thebibliography)\}'
                     r'(?P<content>.*?)\\end\{(?P=kind)\}', re.S)
blocks = []
section = number = subsection = proof = 0
offset = 0
reassembled = []
for match in pattern.finditer(body):
    prose = body[offset:match.start()]
    reassembled.append(prose)
    if prose.strip():
        blocks.append({'type': 'text', 'content': prose.strip()})
    reassembled.append(match.group())
    if match.group('heading'):
        if match.group('heading') == 'section':
            section += 1
            number = subsection = 0
            num = str(section)
        else:
            subsection += 1
            num = f'{section}.{subsection}'
        blocks.append({'type': match.group('heading'), 'title': match.group('title'), 'number': num})
    else:
        kind = match.group('kind')
        content = match.group('content').strip()
        title = ''
        optional = re.match(r'^\[([^\]]*)\]\s*', content)
        if optional:
            title = optional[1]
            content = content[optional.end():]
        if kind == 'thebibliography':
            assert content.startswith('{99}')
            content = content[4:].lstrip()
        if kind in ('lemma', 'proposition', 'corollary'):
            number += 1
            num = f'{section}.{number}'
        elif kind == 'proof':
            proof += 1
            num = str(proof)
        else:
            num = ''
        blocks.append({'type': kind, 'content': content, 'number': num, 'title': title})
    offset = match.end()
tail = body[offset:]
reassembled.append(tail)
if tail.strip():
    blocks.append({'type': 'text', 'content': tail.strip()})
assert ''.join(reassembled) == body
assert section == 6 and proof == 26
assert sum(b['type'] == 'lemma' for b in blocks) == 19
assert sum(b['type'] == 'proposition' for b in blocks) == 7
assert sum(b['type'] == 'corollary' for b in blocks) == 1
data = {'title': re.search(r'\\title\{([^{}]+)\}', text)[1],
        'date': re.search(r'\\date\{([^{}]+)\}', text)[1],
        'source': stem + '.tex', 'sourceSha256': hashlib.sha256(raw).hexdigest(),
        'proofStatus': 'unverified', 'blocks': blocks}
(ROOT / 'threefold-content.json').write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'blocks': len(blocks), 'proofs': proof, 'sections': section, 'source_sha256': data['sourceSha256']}))
