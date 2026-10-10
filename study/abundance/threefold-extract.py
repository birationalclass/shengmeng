"""Extract the approved manuscript, retaining nested statement order."""
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
stem = 'nef-abundance-threefold-behavior-20261010'
raw = (ROOT / (stem + '.tex')).read_bytes()
text = raw.decode('utf-8').replace('\r\n', '\n')
body = text.split(r'\maketitle', 1)[1].rsplit(r'\end{document}', 1)[0]
kinds = 'theorem|setup|lemma|proposition|corollary|proof|thebibliography'
token = re.compile(r'\\(?P<heading>section|subsection)\{' +
                   r'|\\begin\{(?P<kind>' + kinds + r')\}')
environment = re.compile(r'\\(?P<edge>begin|end)\{(?P<kind>[^{}]+)\}')
section = number = subsection = proof = 0


def argument(value, start):
    assert value[start] == '{'
    depth = 1
    for end in range(start + 1, len(value)):
        if value[end - 1] == '\\':
            continue
        if value[end] == '{':
            depth += 1
        elif value[end] == '}':
            depth -= 1
            if depth == 0:
                return value[start + 1:end], end + 1
    raise ValueError('Unclosed heading argument')


def extract(value):
    global section, number, subsection, proof
    blocks, pieces = [], []
    offset = 0
    while match := token.search(value, offset):
        before = value[offset:match.start()]
        pieces.append(before)
        if before.strip():
            blocks.append({'type': 'text', 'content': before.strip()})
        heading, kind = match.group('heading', 'kind')
        if heading:
            title, end = argument(value, match.end() - 1)
            if heading == 'section':
                section += 1
                number = subsection = 0
                num = str(section)
            else:
                subsection += 1
                num = f'{section}.{subsection}'
            blocks.append({'type': heading, 'title': title, 'number': num})
        else:
            stack = [kind]
            for edge in environment.finditer(value, match.end()):
                name = edge['kind']
                if edge['edge'] == 'begin':
                    stack.append(name)
                else:
                    assert stack and stack.pop() == name, 'Unbalanced environment ' + name
                    if not stack:
                        end = edge.end()
                        inside = value[match.end():edge.start()].strip()
                        break
            else:
                raise ValueError('Unclosed environment ' + kind)
            title = ''
            optional = re.match(r'^\[([^\]]*)\]\s*', inside)
            if optional:
                title, inside = optional[1], inside[optional.end():]
            if kind == 'thebibliography':
                assert inside.startswith('{99}')
                inside = inside[4:].lstrip()
            if kind in ('lemma', 'proposition', 'corollary'):
                number += 1
                num = f'{section}.{number}'
            elif kind == 'proof':
                proof += 1
                num = str(proof)
            else:
                num = ''
            block = {'type': kind, 'content': inside, 'number': num, 'title': title}
            if kind == 'proof' and token.search(inside):
                # The opening proof contains its setup and three core statements.
                # Keep these visible; only its final assembly becomes a proof control.
                children = extract(inside)
                assert children[-1]['type'] == 'text'
                completion = children[-1]['content']
                assert completion.startswith('We now complete the proof.')
                block['introduction'] = children[:-1]
                block['content'] = completion[len('We now complete the proof.'):].strip()
                block['completionHeading'] = 'We now complete the proof.'
            blocks.append(block)
        pieces.append(value[match.start():end])
        offset = end
    tail = value[offset:]
    pieces.append(tail)
    if tail.strip():
        blocks.append({'type': 'text', 'content': tail.strip()})
    assert ''.join(pieces) == value, 'Extraction changed source text'
    return blocks


def walk(blocks):
    for block in blocks:
        yield block
        yield from walk(block.get('introduction', []))


blocks = extract(body)
counts = Counter(block['type'] for block in walk(blocks))
for kind in kinds.split('|'):
    assert counts[kind] == len(re.findall(r'\\begin\{' + kind + r'\}', body)), kind
for heading in ('section', 'subsection'):
    assert counts[heading] == len(re.findall(r'\\' + heading + r'\{', body)), heading
structure = dict(counts)
structure['equations'] = len(re.findall(r'\\begin\{equation\}', body))
structure['labels'] = len(re.findall(r'\\label\{', body))
structure['bibliography'] = len(re.findall(r'\\bibitem\{', body))
data = {'title': re.search(r'\\title\{([^{}]+)\}', text)[1],
        'date': re.search(r'\\date\{([^{}]+)\}', text)[1],
        'source': stem + '.tex', 'sourceSha256': hashlib.sha256(raw).hexdigest(),
        'proofStatus': 'unverified', 'structure': structure, 'blocks': blocks}
(ROOT / 'threefold-content.json').write_text(
    json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'structure': structure, 'source_sha256': data['sourceSha256']}))
