"""Usage: python build-chalk-font.py /path/to/MaShanZheng-Regular.ttf.
Requires fonttools and brotli; source is Google Fonts/ofl/mashanzheng (OFL).
"""
import hashlib, json, sys
from pathlib import Path
from fontTools.ttLib import TTFont
from fontTools import subset
root = Path(__file__).resolve().parent
pages = json.loads((root / 'assets/chalk/pages.json').read_text())['pages']
text = ''.join(p['source'] + p['title'] + p.get('author', '') + p['text'] for p in pages) + ' …，。；：（）！？、'
chars = set(text)
source = TTFont(sys.argv[1])
cmap = source.getBestCmap()
missing = [c for c in chars if ord(c) not in cmap and '\u3400' <= c <= '\u9fff']
if missing:
    raise ValueError('Source font lacks Chinese characters: ' + ''.join(sorted(missing)))
target = root / 'assets/fonts/RefugeChinese.woff2'
if target.exists():
    old = TTFont(target).getBestCmap()
    added = sorted(c for c in chars if ord(c) not in old and '\u3400' <= c <= '\u9fff')
    print('Previously missing Chinese characters:', ''.join(added), f'({len(added)})')
options = subset.Options(); options.flavor = 'woff2'
subsetter = subset.Subsetter(options=options); subsetter.populate(text=''.join(chars))
subsetter.subset(source); source.flavor = 'woff2'; source.save(target)
font = TTFont(target)
assert all(ord(c) in font.getBestCmap() for c in chars if '\u3400' <= c <= '\u9fff')
(root / 'assets/fonts/chalk-coverage.json').write_text(json.dumps({
    'source': 'https://github.com/google/fonts/tree/main/ofl/mashanzheng',
    'characters': ''.join(sorted(chars)),
    'sha256': hashlib.sha256(target.read_bytes()).hexdigest()
}, ensure_ascii=False, indent=2) + '\n')
print('Verified Chinese glyph coverage; font bytes:', target.stat().st_size)
