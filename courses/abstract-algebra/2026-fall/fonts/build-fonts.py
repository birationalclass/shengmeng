"""Build the opening's compact OFL web fonts with fonttools and brotli.

Usage: python build-fonts.py /path/to/downloaded-font-sources
Source filenames and URLs are documented in README.md.
"""
from pathlib import Path
import hashlib
import json
import shutil
import sys

from fontTools import subset
from fontTools.ttLib import TTFont
from fontTools.varLib.instancer import instantiateVariableFont

destination = Path(__file__).resolve().parent
semester = destination.parent
sources = Path(sys.argv[1])
text = "".join(path.read_text() for path in [semester / "index.html", *sorted(semester.glob("opening*.js")), *sorted(semester.glob("opening*.css"))])
characters = {ord(character) for character in text}
characters.update(range(0x20, 0x250))
characters.update(range(0x370, 0x400))
characters.update(range(0x2000, 0x20A0))
characters.update(range(0x2190, 0x2300))

jobs = [
    ("SourceSerif4-Roman.ttf", "OpeningSerif-Regular.woff2", "OpeningSerif", "Regular", {"wght": 400, "opsz": 24}),
    ("SourceSerif4-Italic.ttf", "OpeningSerif-Italic.woff2", "OpeningSerif", "Italic", {"wght": 400, "opsz": 24}),
    ("Inter.ttf", "OpeningSans.woff2", "OpeningSans", "Regular", {}),
    ("NotoSerifSC.ttf", "OpeningChinese-Regular.woff2", "OpeningChinese", "Regular", {"wght": 400}),
]
manifest = {"license": "SIL Open Font License 1.1", "files": []}
for source, output, family, style, axes in jobs:
    original = sources / source
    font = TTFont(original)
    if axes:
        font = instantiateVariableFont(font, axes, inplace=True)
    coverage = set(font.getBestCmap()) & characters
    options = subset.Options()
    options.name_IDs = ["*"]
    options.name_legacy = True
    options.name_languages = ["*"]
    options.layout_features = ["*"]
    options.notdef_outline = True
    subsetter = subset.Subsetter(options=options)
    subsetter.populate(unicodes=coverage)
    subsetter.subset(font)
    # Subsets use our own family names; original copyright and license remain.
    names = {1: family, 2: style, 3: family + "-" + style + "-20260914", 4: family + " " + style, 6: family + "-" + style, 16: family, 17: style}
    for record in font["name"].names:
        if record.nameID in names:
            record.string = names[record.nameID].encode(record.getEncoding(), errors="replace")
    font.flavor = "woff2"
    target = destination / output
    font.save(target)
    result = {"file": output, "source": source, "source_sha256": hashlib.sha256(original.read_bytes()).hexdigest(), "axes": axes, "bytes": target.stat().st_size, "codepoints": [f"U+{value:04X}" for value in sorted(coverage)]}
    manifest["files"].append(result)
    print(output, result["bytes"], "bytes", len(coverage), "codepoints", flush=True)
for name in ["OFL-SourceSerif4.txt", "OFL-Inter.txt", "OFL-NotoSerifSC.txt"]:
    shutil.copyfile(sources / name, destination / name)
(destination / "opening-fonts-manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
